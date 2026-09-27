"""Validate and atomically publish M1 typed-model bundles (Linux).

This is an internal API for the forthcoming C driver. It accepts no LLVM IR
and makes no C-equivalence claim. Backend model validation is mandatory.
"""
import ctypes
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile


class ArtifactError(ValueError):
    pass


FILES = {'model.smv', 'properties.json', 'source-map.json', 'provenance.json'}


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ArtifactError('Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(text):
    return json.loads(text, object_pairs_hook=_object)


def check_artifact(artifact):
    if not isinstance(artifact, dict) or set(artifact) != {'version', 'files'} or type(artifact['version']) is not int or artifact['version'] != 1:
        raise ArtifactError('Invalid artifact envelope/version')
    files = artifact['files']
    if not isinstance(files, dict) or set(files) != FILES | {'manifest.json'} or any(not isinstance(v, str) for v in files.values()):
        raise ArtifactError('Unexpected artifact files')
    manifest = read_json(files['manifest.json'])
    if not isinstance(manifest, dict) or set(manifest) != {'version', 'artifact_id', 'files'} or type(manifest['version']) is not int or manifest['version'] != 1:
        raise ArtifactError('Invalid manifest')
    digests = {name: hashlib.sha256(files[name].encode('utf-8')).hexdigest() for name in sorted(FILES)}
    identity = 'llvm2smv-model-v1\n' + ''.join(name + '\n' + digest + '\n' for name, digest in digests.items())
    if manifest['files'] != digests or manifest['artifact_id'] != hashlib.sha256(identity.encode('ascii')).hexdigest():
        raise ArtifactError('Artifact content digest mismatch')
    for name in FILES - {'model.smv'}:
        value = read_json(files[name])
        if not isinstance(value, dict) or type(value.get('version')) is not int or value['version'] != 1:
            raise ArtifactError('Invalid sidecar: ' + name)
    return files


def _rename_new(source, destination):
    # Linux renameat2 gives atomic publication without replacing even an empty
    # destination directory. No check-then-rename overwrite race or fallback.
    libc = ctypes.CDLL(None, use_errno=True)
    try:
        rename = libc.renameat2
    except AttributeError as error:
        raise ArtifactError('Atomic bundle publication requires Linux renameat2') from error
    rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    rename.restype = ctypes.c_int
    if rename(-100, os.fsencode(source), -100, os.fsencode(destination), 1) != 0:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code), str(destination))


def _stop(process):
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.communicate()


def publish(artifact, destination, checker, timeout=30):
    """Publish a new directory only after native model validation.

    Existing destinations (including symlinks) are never replaced. Timeout,
    UNKNOWN, malformed checker output, and errors leave no published bundle.
    The caller supplies the checker installation and its YASMV_HOME environment.
    """
    if type(timeout) not in (float, int) or not math.isfinite(timeout) or timeout <= 0:
        raise ArtifactError('Timeout must be positive and finite')
    files = check_artifact(artifact)
    destination = Path(os.path.abspath(destination))  # Do not resolve destination symlinks.
    if os.path.lexists(destination):
        raise FileExistsError(str(destination))
    staging = Path(tempfile.mkdtemp(prefix='.' + destination.name + '.tmp-', dir=destination.parent))
    try:
        for name, content in files.items():
            (staging / name).write_text(content, encoding='utf-8')
        request = {'version': 1, 'model': str(staging / 'model.smv'),
                   'query': {'operation': 'validate-model', 'limits': {'wall_ms': max(1, int(timeout * 1000))}}}
        request_path = staging / 'validation-request.json'
        request_path.write_text(json.dumps(request), encoding='utf-8')
        process = subprocess.Popen([str(checker), '--quiet', '--query-file', str(request_path)],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True, start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as error:
            _stop(process)
            raise ArtifactError('Model validation timed out') from error
        except BaseException:
            _stop(process)
            raise
        try:
            result = read_json(stdout)
        except (ValueError, TypeError) as error:
            raise ArtifactError('Invalid model validation response') from error
        if (process.returncode != 0 or not isinstance(result, dict)
                or type(result.get('version')) is not int or result.get('version') != 1 or result.get('status') != 'completed'
                or result.get('outcome') != 'valid'):
            raise ArtifactError('Model validation failed: ' + stderr + '\n' + stdout)
        request_path.unlink()
        _rename_new(staging, destination)
        return destination
    finally:
        if staging.exists():
            shutil.rmtree(staging)
