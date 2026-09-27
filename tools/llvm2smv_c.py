"""Controlled LLVM 18 C workflow. Model replay does not certify translation."""
import argparse
import hashlib
import json
import math
import os
import shutil
from pathlib import Path
import re
import subprocess
import tempfile

from llvm2smv_artifact import ArtifactError, ArtifactUnknown, FILES, check_artifact, publish, read_json, _stop

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / 'llvm2smv/runtime'
FLAGS = ['-std=c11', '-O0', '-g', '-fno-finite-loops', '-Werror=implicit-function-declaration']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(command, timeout, input=None):
    process = subprocess.Popen([str(arg) for arg in command], stdin=subprocess.PIPE if input is not None else None,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        stdout, stderr = process.communicate(input, timeout=timeout)
    except BaseException:
        _stop(process)
        raise
    return process.returncode, stdout, stderr


def checked(command, timeout, input=None):
    code, stdout, stderr = run(command, timeout, input)
    if code:
        raise ArtifactError(f'{command[0]} failed ({code}): {stderr or stdout}')
    return stdout


def seal(files):
    """Use the M1 content identity after adding controlled build provenance."""
    files = dict(files)
    hashes = {name: digest(files[name].encode('utf-8')) for name in sorted(FILES)}
    identity = 'llvm2smv-model-v1\n' + ''.join(name + '\n' + value + '\n' for name, value in hashes.items())
    files['manifest.json'] = json.dumps(dict(version=1, artifact_id=digest(identity.encode('ascii')), files=hashes), sort_keys=True) + '\n'
    result = dict(version=1, files=files)
    check_artifact(result)
    return result


def compile_candidate(args, temporary):
    capabilities = read_json(checked([args.translator, '--capabilities'], args.timeout))
    version = capabilities.get('llvm_version')
    if not isinstance(version, str) or not version.startswith('18.'):
        raise ArtifactError('Translator must use LLVM 18')
    tools = {}
    for name in ('clang', 'llvm_link'):
        executable = getattr(args, name)
        banner = checked([executable, '--version'], args.timeout)
        match = re.search(r'\bversion\s+(\d+\.\d+\.\d+)\b', banner)
        if not match or match[1] != version:
            raise ArtifactError('Clang, llvm-link, and translator LLVM versions must match exactly')
        binary = Path(shutil.which(executable) or executable).resolve(strict=True)
        tools[name] = dict(executable=str(binary), sha256=digest(binary.read_bytes()), version=match[1], banner=banner)
    includes = [str(Path(path).resolve()) for path in args.include]
    if any(value.split('=', 1)[0] == 'NDEBUG' for value in args.define):
        raise ArtifactError('NDEBUG disables assertions and is unsupported')
    options = ['-I', str(RUNTIME)] + [arg for path in includes for arg in ('-I', path)] + ['-D' + value for value in args.define]
    records, objects = [], []
    for index, source in enumerate(args.sources):
        source = source.resolve(strict=True)
        if source.suffix != '.c':
            raise ArtifactError('The controlled driver accepts C translation units (.c)')
        # Compile the exact preprocessed snapshot. It contains expanded headers
        # and line directives; the compiler never rereads mutable user headers.
        preprocessed = checked([args.clang, *FLAGS, *options, '-E', str(source)], args.timeout)
        if re.search(r'^\s*#\s*pragma\b', preprocessed, re.MULTILINE):
            raise ArtifactError('Source pragmas require an explicit semantic policy')
        obj = temporary / f'unit-{index}.bc'
        checked([args.clang, *FLAGS, '-x', 'cpp-output', '-emit-llvm', '-c', '-', '-o', obj],
                args.timeout, input=preprocessed)
        records.append(dict(path=str(source), preprocessed_sha256=digest(preprocessed.encode()),
                            preprocessed=preprocessed))
        objects.append(obj)
    linked = temporary / 'linked.bc'
    checked([args.llvm_link, *objects, '-o', linked], args.timeout)
    artifact = read_json(checked([args.translator, '--emit-scalar-bundle', '--diagnostics=json',
                                 '--entry=' + args.entry, linked], args.timeout))
    files = check_artifact(artifact)
    provenance = read_json(files['provenance.json'])
    provenance['c_build'] = dict(policy='clang18-scalar-c-v1', tools=tools, flags=FLAGS,
        include_paths=includes, defines=args.define, entry=args.entry,
        units=records, runtime={p.name: digest(p.read_bytes()) for p in sorted(RUNTIME.glob('*.h'))},
        assertions='controlled assert.h and __VERIFIER_assert; NDEBUG rejected',
        error_scope='admitted LLVM UB uses, not complete ISO C undefined behavior detection')
    files['provenance.json'] = json.dumps(provenance, sort_keys=True) + '\n'
    return seal(files)


def query(checker, bundle, temporary, timeout, request):
    path = temporary / 'query.json'
    path.write_text(json.dumps(dict(version=1, model=str(bundle / 'model.smv'), query=request)))
    code, stdout, stderr = run([checker, '--quiet', '--query-file', path], timeout)
    try:
        result = read_json(stdout)
    except ValueError as error:
        raise ArtifactError('Invalid checker response: ' + stderr) from error
    if (not isinstance(result, dict) or result.get('version') != 1 or code not in (0, 3)
            or result.get('status') not in ('completed', 'unknown')):
        raise ArtifactError('Checker failed: ' + stdout + stderr)
    if code == 3 and result['status'] != 'unknown':
        raise ArtifactError('Inconsistent checker exit status')
    return result


def prop(name):
    return 'p_' + name.encode().hex()


def project(trace, source_map):
    """Project only replayed model frames; absent C variable locations stay absent."""
    locations = source_map['locations']
    frames = []
    for frame in trace['steps']:
        values = frame['values']
        pc = values['v_7063']
        location = locations.get(pc)
        record = dict(step=frame['step'], pc=pc, location=location)
        if location and 'choice_symbol' in location:
            record['nondeterministic_value'] = values[location['choice_symbol']]
        record['globals'] = {bytes.fromhex(detail['key_hex']).decode(errors='backslashreplace')[7:]: dict(bits=values[symbol],
                                  poison=values.get('v_' + (b'global-poison.' + bytes.fromhex(detail['key_hex'])[7:]).hex()))
                             for symbol, detail in source_map['symbols'].items()
                             if bytes.fromhex(detail['key_hex']).startswith(b'global.')}
        frames.append(record)
    return dict(version=1, kind='model-trace-source-projection', frames=frames,
                local_variables='unavailable', translation_independently_certified=False)


def check(args, bundle, temporary):
    # Recheck the stored payload identity before pairing model results with source metadata.
    artifact = dict(version=1, files={name: (bundle / name).read_text() for name in FILES | {'manifest.json'}})
    files = check_artifact(artifact)
    manifest = read_json(files['manifest.json'])
    source_map = read_json(files['source-map.json'])
    # Query a private snapshot of the checked bytes, so later changes to the
    # published directory cannot pair a different model with these sidecars.
    snapshot = temporary / 'checked-model'
    snapshot.mkdir()
    (snapshot / 'model.smv').write_text(files['model.smv'])
    def ask(request):
        return query(args.checker, snapshot, temporary, args.timeout, request)
    wall = max(1, int(args.timeout * 1000))
    initial = ask(dict(operation='check-init', limits=dict(wall_ms=wall)))
    report = dict(version=1, status='unknown', check=args.check, artifact_id=manifest['artifact_id'],
                  bundle=str(bundle), scope='configured LLVM scalar model',
                  assumptions='false verifier assumptions exit to ASSUMED_OUT; no fairness',
                  translation_certified=False, admitted_execution='unknown', trace=None, source_trace=None)
    if initial['status'] == 'unknown':
        report['backend'] = initial
        return report
    if initial['outcome'] != 'satisfiable':
        raise ArtifactError('Generated model has no initial execution')
    if args.check == 'termination':
        request = dict(operation='check-progress', target=prop('progress_goal'), limits=dict(states=args.states, wall_ms=wall))
    else:
        request = dict(operation='prove-property' if args.prove else 'check-property',
                       property=dict(name='scalar_safety', expression=prop('safe')),
                       limits=dict(depth=args.depth, wall_ms=wall))
    result = ask(request)
    report['backend'] = result
    if result['status'] == 'unknown':
        return report
    outcome = result.get('outcome')
    if args.check == 'termination':
        if outcome not in ('proven', 'violated') or not result.get('progress'):
            raise ArtifactError('Unexpected progress response')
        replay = ask(dict(operation='validate-progress', progress=result['progress'], limits=dict(states=args.states, wall_ms=wall)))
        report['replay'] = replay
        if replay.get('outcome') != 'valid':
            return report
        report['status'] = 'proven_for_model' if outcome == 'proven' else 'violation'
        if outcome == 'violated':
            report['trace'] = result['progress']['trace']
            report['source_trace'] = project(report['trace'], source_map)
            report['failure_kind'] = 'progress_' + result['progress']['kind']
            report['loop_start'] = result['progress'].get('loop_start')
        # Prove exclusion separately. A bounded absence of normal exit is not vacuity.
        vacuity = ask(dict(operation='check-progress', target=prop('assumed_out'), limits=dict(states=args.states, wall_ms=wall)))
        report['admission_check'] = vacuity
        report['admitted_execution'] = 'unknown'
        if vacuity.get('outcome') == 'proven':
            validation = ask(dict(operation='validate-progress', progress=vacuity['progress'], limits=dict(states=args.states, wall_ms=wall)))
            report['admission_replay'] = validation
            if validation.get('outcome') == 'valid':
                report['status'] = 'no_admitted_execution'
                report['admitted_execution'] = False
        return report
    if outcome == 'violated':
        trace = result.get('trace')
        if not trace:
            raise ArtifactError('Violation has no trace')
        replay = ask(dict(operation='validate-trace', trace=trace, limits=dict(wall_ms=wall)))
        report['replay'] = replay
        if replay.get('outcome') != 'valid':
            return report
        report.update(status='violation', trace=trace, source_trace=project(trace, source_map))
        frames = report['source_trace']['frames']
        report['failure_site'] = frames[-2]['location'] if len(frames) > 1 else None
        report['failure_kind'] = 'runtime_error' if frames[-1]['pc'] == 'e_7063_4552524f52' else 'assertion'
    elif outcome == 'holds_bounded':
        if result.get('scope') != 'through_depth':
            raise ArtifactError('Unexpected bounded result scope')
        report.update(status='holds_through_depth', depth=args.depth, unbounded_outcome='unknown')
    elif outcome == 'proven' and result.get('scope') == 'unbounded' and result.get('proof', {}).get('verified'):
        report['status'] = 'proven_for_model'
    else:
        raise ArtifactError('Unexpected safety result')
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources', nargs='+', type=Path)
    parser.add_argument('-o', '--output', required=True, type=Path, help='New validated bundle directory')
    parser.add_argument('--entry', default='main')
    parser.add_argument('--check', choices=('safety', 'termination'), default='safety')
    parser.add_argument('--depth', type=int, default=100, help='Safety bound in model transitions')
    parser.add_argument('--prove', action='store_true', help='Try safety induction through --depth')
    parser.add_argument('--states', type=int, default=1000, help='Progress exploration budget')
    parser.add_argument('--timeout', type=float, default=30, help='Wall seconds per tool/query process')
    parser.add_argument('-I', '--include', action='append', default=[])
    parser.add_argument('-D', '--define', action='append', default=[])
    parser.add_argument('--clang', default=os.environ.get('CLANG', 'clang-18'))
    parser.add_argument('--llvm-link', default=os.environ.get('LLVM_LINK', 'llvm-link-18'))
    parser.add_argument('--translator', default=os.environ.get('LLVM2SMV', str(ROOT / 'llvm2smv/llvm2smv')))
    parser.add_argument('--checker', default=os.environ.get('YASMV', str(ROOT / 'yasmv')))
    args = parser.parse_intermixed_args(argv)
    os.environ.setdefault('YASMV_HOME', str(ROOT))
    report = None
    try:
        if not math.isfinite(args.timeout) or args.timeout <= 0 or args.depth < 0 or args.states < 1:
            raise ArtifactError('Timeout/states must be positive; depth must be nonnegative')
        if args.prove and args.check != 'safety':
            raise ArtifactError('--prove applies only to safety')
        if os.path.lexists(args.output):
            raise FileExistsError(str(args.output))
        with tempfile.TemporaryDirectory(prefix='llvm2smv-c-') as directory:
            temporary = Path(directory)
            artifact = compile_candidate(args, temporary)
            bundle = publish(artifact, args.output, args.checker, timeout=args.timeout)
            report = check(args, bundle, temporary)
    except ArtifactUnknown as error:
        report = dict(version=1, status='unknown', reason=str(error), verification_result=None)
    except subprocess.TimeoutExpired:
        report = dict(version=1, status='unknown', reason='tool_wall_timeout', verification_result=None)
    except (OSError, ValueError) as error:
        report = dict(version=1, status='error', message=str(error), verification_result=None)
    except KeyboardInterrupt:
        report = dict(version=1, status='unknown', reason='cancelled', verification_result=None)
    print(json.dumps(report, sort_keys=True))
    return {'error': 2, 'unknown': 3, 'violation': 1}.get(report['status'], 0)
