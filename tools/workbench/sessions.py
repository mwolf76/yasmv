"""Owned immutable model processes; every query executes in a disposable fork.

A session is published only after the checker validates and compiles its model.
The pool is bounded, serializes each snapshot, and destroys cancelled sessions.
No legacy C++ manager is shared between concurrently executing queries.
"""
import hashlib
import os
from pathlib import Path
import selectors
import signal
import subprocess
import tempfile
import threading
import time

from . import protocol


class LoadError(ValueError):
    def __init__(self, result):
        super().__init__("Snapshot load failed: " + str(result.get("diagnostics", [])))
        self.result = result


class Interrupted(Exception):
    pass


def check(cancel, deadline):
    if cancel.is_set() or time.monotonic() >= deadline:
        raise Interrupted('cancelled' if cancel.is_set() else 'deadline')


def fingerprint(binary, home, revision, cancel=None, deadline=None):
    # Include actual bytes, not only mtimes: same-size replacement also invalidates.
    h = hashlib.sha256()
    for path in [Path(binary), *sorted((Path(home) / 'microcode').glob('*.json'))]:
        h.update(str(path.resolve()).encode() + b'\0')
        with path.open('rb') as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b''):
                if cancel is not None:
                    check(cancel, deadline)
                h.update(chunk)
    from .engine import encoded
    h.update(encoded(dict(source=revision['source'], root=revision['root'], inputs=revision['inputs'])))
    return h.hexdigest()


class Session:
    def __init__(self, binary, home, revision, cancel, deadline):
        from .engine import atomic
        self.temp = tempfile.TemporaryDirectory(prefix='yasmv-session-')
        self.process = None
        self.stderr = None
        self.lock = threading.Lock()
        self.buffer = bytearray()
        self.used = time.monotonic()
        try:
            directory = Path(self.temp.name)
            (directory / 'model.smv').write_text(revision['source'])
            atomic(directory / 'load.json', dict(version=1, model=str(directory / 'model.smv'), inputs=revision['inputs']))
            self.stderr = (directory / 'stderr.log').open('wb')
            args = [binary, '--quiet', '--session-file', str(directory / 'load.json')]
            if revision['root']:
                args += ['--root', revision['root']]
            self.process = subprocess.Popen(args, cwd=directory, env=dict(os.environ, YASMV_HOME=home),
                                            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr,
                                            start_new_session=True, bufsize=0)
            self.ready = self.read(cancel, deadline)
            if self.ready.get('status') != 'ready':
                raise LoadError(self.ready)
        except BaseException:
            self.close()
            raise

    def read(self, cancel, deadline):
        with selectors.DefaultSelector() as selector:
            selector.register(self.process.stdout, selectors.EVENT_READ)
            while b'\n' not in self.buffer:
                check(cancel, deadline)
                if selector.select(min(.04, max(0, deadline - time.monotonic()))):
                    data = os.read(self.process.stdout.fileno(), 65536)
                    if not data:
                        raise ValueError('Snapshot worker closed its output')
                    self.buffer.extend(data)
                    if len(self.buffer) > 16 * 1024 * 1024:
                        raise ValueError('Snapshot result exceeds 16 MiB')
            line, _, rest = self.buffer.partition(b'\n')
            self.buffer = bytearray(rest)
            return protocol.loads(line.decode())

    def query(self, query, cancel, deadline):
        from .engine import encoded
        check(cancel, deadline)
        # Nonblocking writes preserve cancellation for large imported traces.
        data = memoryview(encoded(query) + b'\n')
        fd = self.process.stdin.fileno()
        os.set_blocking(fd, False)
        with selectors.DefaultSelector() as selector:
            selector.register(fd, selectors.EVENT_WRITE)
            while data:
                check(cancel, deadline)
                if selector.select(.04):
                    try:
                        data = data[os.write(fd, data[:65536]):]
                    except BlockingIOError:
                        pass
        result = self.read(cancel, deadline)
        if not isinstance(result, dict) or result.get('version') != 1 or result.get('request_id') != query['request_id'] or result.get('status') not in ('completed', 'unknown', 'error'):
            raise ValueError('Malformed snapshot result')
        self.used = time.monotonic()
        return result

    def close(self):
        if self.process is not None:
            # Let the snapshot kill and reap its child before exiting.
            self.process.stdin.close()
            try:
                os.kill(self.process.pid, signal.SIGCONT)
                os.kill(self.process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                self.process.wait(timeout=.5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(self.process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                self.process.wait()
            self.process.stdout.close()
            self.process = None
        if self.stderr is not None:
            self.stderr.close()
            self.stderr = None
        self.temp.cleanup()


class Pool:
    def __init__(self, capacity=4):
        self.capacity = capacity
        self.guard = threading.Lock()
        self.sessions = {}
        self.closed = False

    def run(self, binary, home, revision, query, cancel, deadline):
        check(cancel, deadline)
        key = fingerprint(binary, home, revision, cancel, deadline)
        session = None
        while session is None:
            check(cancel, deadline)
            if not self.guard.acquire(timeout=.04):
                continue
            try:
                if self.closed:
                    raise ValueError('Session pool closed')
                candidate = self.sessions.get(key)
                hit = candidate is not None
                if candidate is None:
                    candidate = Session(binary, home, revision, cancel, deadline)
                    try:
                        if fingerprint(binary, home, revision, cancel, deadline) != key:
                            raise ValueError('Checker or microcode changed while loading the snapshot; retry the query')
                        check(cancel, deadline)
                        if len(self.sessions) >= self.capacity:
                            idle = [(s.used, k, s) for k, s in self.sessions.items() if not s.lock.locked()]
                            if not idle:
                                raise ValueError('All compiled sessions are busy')
                            _, victim, old = min(idle)
                            old.close()
                            del self.sessions[victim]
                    except BaseException:
                        candidate.close()
                        raise
                    self.sessions[key] = candidate
                if candidate.lock.acquire(blocking=False):
                    if candidate.process is None:
                        candidate.lock.release()
                        del self.sessions[key]
                    else:
                        session = candidate
            finally:
                self.guard.release()
            if session is None:
                cancel.wait(.02)
        try:
            result = session.query(query, cancel, deadline)
            result.setdefault('statistics', {}).update(session_cache_hit=hit, session_key=key,
                                                      session_load_ms=session.ready['load_ms'])
            return result
        except BaseException:
            # Detach before releasing the lease; waiters retry via a fresh snapshot.
            # Keep lock order guard -> session consistent by releasing first.
            session.close()
            raise
        finally:
            session.lock.release()
            with self.guard:
                if session.process is None and self.sessions.get(key) is session:
                    del self.sessions[key]

    def close(self):
        with self.guard:
            self.closed = True
            for session in self.sessions.values():
                session.close()
            self.sessions.clear()
