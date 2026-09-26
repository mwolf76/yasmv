"""Immutable revisions, isolated workers and atomic results for the local workbench."""
from copy import deepcopy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time
import uuid

from . import protocol

ROOT = Path(__file__).resolve().parents[2]


def encoded(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(',', ':'), allow_nan=False).encode()


def atomic(path, value):
    path = Path(path)
    temporary = path.with_name('.' + path.name + '.' + uuid.uuid4().hex)
    try:
        with temporary.open('xb') as stream:
            stream.write(encoded(value) + b'\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def read(path):
    return protocol.loads(Path(path).read_text())


class Engine:
    def __init__(self, directory, binary=None, home=None):
        self.directory = Path(directory).resolve()
        self.directory.mkdir(parents=True, exist_ok=True, mode=0o700)
        self.lockfile = (self.directory / 'owner.lock').open('a')
        try:
            fcntl.flock(self.lockfile, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            self.lockfile.close()
            raise ValueError('This artifact store is already open by another runner') from None
        self.binary = str(Path(binary or ROOT / 'yasmv').resolve())
        self.home = str(Path(home or ROOT).resolve())
        self.guard = threading.RLock()
        self.active = {}
        self.closed = False
        for kind in ('revisions', 'jobs', 'traces'):
            (self.directory / kind).mkdir(exist_ok=True)
        for directory in (self.directory / 'jobs').iterdir():
            if not directory.is_dir() or not (directory / 'request.json').exists():
                continue
            if not (directory / 'result.json').exists():
                result = protocol.failure(directory.name, 'worker_interrupted', 'Runner stopped before publishing a result', True)
                atomic(directory / 'result.json', result)
            events = self.events(directory.name)
            if not any(e['event'] == 'result' for e in events):
                self.emit(directory.name, 'result', result=read(directory / 'result.json'))

    def path(self, kind, identifier):
        if not isinstance(identifier, str) or not protocol.ID.fullmatch(identifier):
            raise ValueError('Invalid artifact identifier')
        return self.directory / kind / identifier

    def save_revision(self, value):
        value = protocol.revision(value)
        identifier = hashlib.sha256(encoded(value)).hexdigest()
        with self.guard:
            directory = self.path('revisions', identifier)
            directory.mkdir(exist_ok=True)
            if not (directory / 'revision.json').exists():
                source = directory / 'model.smv'
                temp = directory / ('.source-' + uuid.uuid4().hex)
                temp.write_text(value['source'])
                temp.replace(source)
                atomic(directory / 'revision.json', dict(value, id=identifier))
        return self.revision(identifier)

    def revision(self, identifier):
        return read(self.path('revisions', identifier) / 'revision.json')

    def revisions(self):
        return [dict(id=v['id'], name=v['name']) for p in sorted((self.directory / 'revisions').glob('*/revision.json'))
                for v in [read(p)]]

    def trace(self, identifier):
        return read(self.path('traces', identifier).with_suffix('.json'))

    def traces(self, revision=None):
        values = [read(p) for p in (self.directory / 'traces').glob('*.json')]
        return [dict(id=v['id'], revision=v['revision'], job=v['job'], validated=v['validated'],
                     steps=len(v['trace']['steps']), operation=v['trace']['query']['operation'])
                for v in values if revision is None or v['revision'] == revision]

    def events(self, identifier, after=-1):
        path = self.path('jobs', identifier) / 'events.jsonl'
        if not path.exists():
            return []
        lines = path.read_bytes().splitlines(keepends=True)
        return [event for line in lines if line.endswith(b'\n')
                for event in [protocol.loads(line.decode())] if event['seq'] > after]

    def emit(self, identifier, event, **extra):
        with self.guard:
            history = self.events(identifier)
            if history and history[-1]['event'] == 'result':
                return
            entry = dict(version=protocol.VERSION, request_id=identifier, seq=len(history), event=event, **extra)
            path = self.path('jobs', identifier) / 'events.jsonl'
            # Discard only an incomplete last line left by a runner crash.
            if path.exists():
                data = path.read_bytes()
                complete = data.rfind(b'\n') + 1
                if complete != len(data):
                    with path.open('r+b') as stream:
                        stream.truncate(complete)
            with path.open('ab') as stream:
                stream.write(encoded(entry) + b'\n')
                stream.flush()
                os.fsync(stream.fileno())

    def submit(self, value):
        value = deepcopy(protocol.request(value))
        rev = self.revision(value['revision'])
        q = value['query']
        if 'trace_id' in q:
            artifact = self.trace(q['trace_id'])
            if artifact['revision'] != rev['id'] or not artifact['validated']:
                raise ValueError('Trace belongs to a different revision or has not passed replay')
        identifier = value['request_id']
        with self.guard:
            if self.closed:
                raise ValueError('Runner is shutting down')
            if len(self.active) >= 4:
                raise ValueError('Four jobs are already active; wait or cancel a job')
            directory = self.path('jobs', identifier)
            try:
                directory.mkdir()
            except FileExistsError:
                raise ValueError('Request ID already exists') from None
            atomic(directory / 'request.json', value)
            cancel = threading.Event()
            thread = threading.Thread(target=self.run, args=(value, rev, cancel), name='job-' + identifier)
            self.active[identifier] = (thread, cancel)
            self.emit(identifier, 'started', revision=rev['id'], operation=q['operation'])
            thread.start()
        return identifier

    def cancel(self, identifier):
        with self.guard:
            if identifier in self.active:
                self.active[identifier][1].set()
                return True
            return False

    def job(self, identifier):
        directory = self.path('jobs', identifier)
        request = read(directory / 'request.json')
        result = read(directory / 'result.json') if (directory / 'result.json').exists() else None
        return dict(request=request, result=result, running=result is None)

    def jobs(self):
        return [self.job(p.name) for p in sorted((self.directory / 'jobs').iterdir(), key=lambda p: p.stat().st_mtime_ns)
                if (p / 'request.json').exists()]

    @staticmethod
    def terminate(proc):
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=0.3)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()

    def worker(self, request, rev, query, cancel, deadline, stage):
        identifier = request['request_id']
        directory = self.path('jobs', identifier)
        payload = dict(version=1, model=str(self.path('revisions', rev['id']) / 'model.smv'),
                       inputs=rev['inputs'], query=dict(query, request_id=identifier))
        path = directory / (stage + '-request.json')
        atomic(path, payload)
        args = [self.binary, '--quiet', '--query-file', str(path)]
        if rev['root']:
            args += ['--root', rev['root']]
        env = dict(os.environ, YASMV_HOME=self.home)
        started = time.monotonic()
        self.emit(identifier, 'progress', phase=stage, elapsed_ms=0)
        with (directory / (stage + '-stdout.json')).open('wb') as out, (directory / (stage + '-stderr.log')).open('wb') as err:
            proc = subprocess.Popen(args, cwd=directory, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                tick = started
                while proc.poll() is None:
                    if cancel.is_set() or time.monotonic() >= deadline:
                        self.terminate(proc)
                        return protocol.failure(identifier, 'cancelled' if cancel.is_set() else 'deadline',
                                                'Job cancelled' if cancel.is_set() else 'Hard deadline exceeded', True)
                    now = time.monotonic()
                    if now - tick >= 0.5:
                        self.emit(identifier, 'progress', phase=stage, elapsed_ms=round((now - started) * 1000))
                        tick = now
                    cancel.wait(0.04)
            finally:
                if proc.poll() is None:
                    self.terminate(proc)
        output = directory / (stage + '-stdout.json')
        if output.stat().st_size > 16 * 1024 * 1024:
            raise ValueError('Worker result exceeds 16 MiB')
        try:
            result = read(output)
            if not isinstance(result, dict) or result.get('version') != 1 or result.get('status') not in ('completed', 'unknown', 'error'):
                raise ValueError('Malformed worker result')
            expected = 0 if result['status'] == 'completed' else 3 if result['status'] == 'unknown' else 4 if result.get('stop_reason') == 'internal_error' else 2
            if proc.returncode != expected or result.get('request_id') != identifier:
                raise ValueError('Worker exit status or request ID disagrees with result')
            return result
        except (ValueError, UnicodeError) as error:
            return protocol.failure(identifier, 'worker_failed', f'{stage} worker exited {proc.returncode}: {error}. See {stage}-stderr.log')

    def run(self, request, rev, cancel):
        identifier = request['request_id']
        directory = self.path('jobs', identifier)
        result = None
        try:
            query = deepcopy(request['query'])
            if 'trace_id' in query:
                query['trace'] = self.trace(query.pop('trace_id'))['trace']
            query.setdefault('watches', rev['watches'])
            deadline = time.monotonic() + request.get('hard_timeout', 60)
            result = self.worker(request, rev, query, cancel, deadline, 'analysis')
            trace = result.get('trace')
            if trace is not None and result['status'] == 'completed':
                if query['operation'] == 'validate-trace':
                    replay = result
                else:
                    replay = self.worker(request, rev, dict(operation='validate-trace', trace=trace,
                                         watches=query['watches']), cancel, deadline, 'replay')
                if replay['status'] != 'completed' or replay.get('outcome') != 'valid':
                    if replay['status'] == 'completed':
                        replay = protocol.failure(identifier, 'replay_failed', 'Generated trace did not pass replay')
                    result = replay
                    result['trace'] = None
                else:
                    artifact = dict(revision=rev['id'], trace=trace, validated=True,
                                    watches=replay.get('watches') or {}, watch_expressions=query['watches'], job=identifier)
                    trace_id = hashlib.sha256(encoded(dict(revision=rev['id'], trace=trace, watches=artifact['watches'], watch_expressions=query['watches']))).hexdigest()
                    artifact['id'] = trace_id
                    with self.guard:
                        if not cancel.is_set():
                            target = self.path('traces', trace_id).with_suffix('.json')
                            if not target.exists():
                                atomic(target, artifact)
                            result['trace_id'] = trace_id
                            result['trace_validated'] = True
                            result['watches'] = artifact['watches']
        except Exception as error:
            result = protocol.failure(identifier, 'worker_failed', str(error))
        finally:
            with self.guard:
                if cancel.is_set():
                    result = protocol.failure(identifier, 'cancelled', 'Job cancelled', True)
                if result is None:
                    result = protocol.failure(identifier, 'worker_failed', 'Worker stopped unexpectedly')
                atomic(directory / 'result.json', result)
                self.emit(identifier, 'result', result=result)
                self.active.pop(identifier, None)

    def close(self):
        with self.guard:
            self.closed = True
            threads = list(self.active.values())
            for _, cancel in threads:
                cancel.set()
        for thread, _ in threads:
            thread.join()
        fcntl.flock(self.lockfile, fcntl.LOCK_UN)
        self.lockfile.close()
