#!/usr/bin/env python3
"""Lifecycle, cancellation, cache invalidation and process isolation gates."""
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.workbench.engine import Engine
from tools.workbench.sessions import Pool, Session, Interrupted, fingerprint
TOGGLE = (ROOT / 'tests/models/query.smv').read_text()


class SessionTests(unittest.TestCase):
    def setUp(self):
        self.pool = Pool(capacity=2)
        self.addCleanup(self.pool.close)
        self.revision = dict(source=TOGGLE, root='', inputs={})

    def run_query(self, query=None, revision=None, **kwargs):
        return self.pool.run(str(ROOT / 'yasmv'), str(ROOT), revision or self.revision,
                             query or dict(request_id='q', operation='shortest-reach', target='x', limits={'depth': 3}),
                             kwargs.get('cancel', threading.Event()), kwargs.get('deadline', time.monotonic() + 90))

    def test_fresh_equivalence_and_repeated_child_reclamation(self):
        result = self.run_query()
        self.assertFalse(result['statistics']['session_cache_hit'])
        session = next(iter(self.pool.sessions.values()))
        pid = session.process.pid
        self.assertTrue(self.run_query()['statistics']['session_cache_hit'])
        initial_rss = int(Path(f'/proc/{pid}/statm').read_text().split()[1])
        for i in range(12):
            result = self.run_query(dict(request_id=str(i), operation='shortest-reach', target='x' if i % 2 else '!x', limits={'depth': 3}))
            self.assertEqual(result['optimality']['depth'], i % 2)
        time.sleep(.05)
        self.assertEqual(Path(f'/proc/{pid}/task/{pid}/children').read_text().strip(), '')
        self.assertLessEqual(int(Path(f'/proc/{pid}/statm').read_text().split()[1]), initial_rss + 256)
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory)
            (p / 'model.smv').write_text(TOGGLE)
            (p / 'request.json').write_text(json.dumps(dict(version=1, model=str(p / 'model.smv'), query=dict(operation='shortest-reach', target='x', limits={'depth': 3}))))
            fresh = subprocess.run([str(ROOT / 'yasmv'), '--quiet', '--query-file', str(p / 'request.json')], env=dict(os.environ, YASMV_HOME=str(ROOT)), capture_output=True, text=True, timeout=90)
            self.assertEqual(fresh.returncode, 0, fresh.stderr)
            value = json.loads(fresh.stdout)
            self.assertEqual(value['identity'], result['identity'])
            self.assertEqual(value['optimality'], result['optimality'])
            self.assertEqual(value['trace']['steps'], result['trace']['steps'])
        self.pool.close()
        self.assertFalse(Path(f'/proc/{pid}').exists())

    def test_transactional_failed_load_and_eviction(self):
        first = self.run_query()
        good = next(iter(self.pool.sessions.values())).process.pid
        with self.assertRaises(ValueError):
            self.run_query(revision=dict(self.revision, source='MODULE main\nVAR x : unknown_type;'))
        self.assertEqual(self.run_query()['identity'], first['identity'])
        self.assertEqual(next(iter(self.pool.sessions.values())).process.pid, good)
        for i in range(3):
            self.run_query(revision=dict(self.revision, source=TOGGLE + f'\n-- revision {i}\n'))
        self.assertEqual(len(self.pool.sessions), 2)
        self.assertFalse(Path(f'/proc/{good}').exists())

    def test_concurrent_queries_and_revisions_are_isolated(self):
        other = dict(self.revision, source=TOGGLE.replace('INIT !x;', 'INIT x;'))
        def work(i):
            q = dict(request_id=str(i), operation='shortest-reach', target='x', assumptions=['x'] if i % 3 == 0 else [], limits={'depth': 2})
            return i, self.run_query(q, other if i % 2 else self.revision)
        with ThreadPoolExecutor(max_workers=4) as executor:
            results = list(executor.map(work, range(12)))
        for i, r in results:
            self.assertEqual(r['request_id'], str(i))
            if i % 3 == 0 and not i % 2:
                self.assertEqual(r['outcome'], 'unreachable')
            else:
                self.assertEqual(r['optimality']['depth'], 0 if i % 2 else 1)

    def test_cancellation_and_crash_do_not_poison_replacement(self):
        self.run_query()
        session = next(iter(self.pool.sessions.values()))
        pid = session.process.pid
        os.kill(pid, signal.SIGSTOP)
        cancel = threading.Event()
        timer = threading.Timer(.5, cancel.set); timer.start()
        try:
            with self.assertRaises(Interrupted):
                self.run_query(cancel=cancel)
        finally:
            timer.join()
        self.assertFalse(Path(f'/proc/{pid}').exists())
        self.assertEqual(self.run_query()['outcome'], 'reachable')
        session = next(iter(self.pool.sessions.values()))
        os.kill(session.process.pid, signal.SIGKILL)
        session.process.wait()
        with self.assertRaises((OSError, ValueError)):
            self.run_query()
        self.assertEqual(self.run_query()['outcome'], 'reachable')

    def test_cancelled_active_child_is_reaped(self):
        self.run_query()
        session = next(iter(self.pool.sessions.values()))
        parent = session.process.pid
        cancel = threading.Event()
        query = dict(request_id='long', operation='shortest-reach', target='FALSE', limits={'depth': 10000})
        with ThreadPoolExecutor(max_workers=1) as executor:
            pending = executor.submit(self.run_query, query, cancel=cancel)
            children = Path(f'/proc/{parent}/task/{parent}/children')
            end = time.monotonic() + 10
            child = None
            while time.monotonic() < end:
                ids = children.read_text().split()
                if ids:
                    child = int(ids[0])
                    os.kill(child, signal.SIGSTOP)
                    break
                time.sleep(.01)
            self.assertIsNotNone(child)
            cancel.set()
            with self.assertRaises(Interrupted): pending.result(timeout=10)
        self.assertFalse(Path(f'/proc/{child}').exists())
        self.assertFalse(Path(f'/proc/{parent}').exists())
        self.assertEqual(self.run_query()['outcome'], 'reachable')

    def test_input_root_and_content_keys(self):
        # Fingerprint checks actual content, including same-size, restored-mtime edits.
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory); (p / 'microcode').mkdir()
            binary = p / 'checker'; binary.write_bytes(b'one')
            fragment = p / 'microcode/f.json'; fragment.write_text('{}')
            key = fingerprint(binary, p, self.revision)
            stat = fragment.stat(); fragment.write_text('[]'); os.utime(fragment, ns=(stat.st_atime_ns, stat.st_mtime_ns))
            current = fingerprint(binary, p, self.revision)
            self.assertNotEqual(key, current)
            self.assertNotEqual(current, fingerprint(binary, p, dict(self.revision, root='other')))
            stat = binary.stat(); binary.write_bytes(b'two'); os.utime(binary, ns=(stat.st_atime_ns, stat.st_mtime_ns))
            self.assertNotEqual(current, fingerprint(binary, p, self.revision))
        source = 'MODULE main\n#input VAR p : boolean;\n#inertial\nVAR x : boolean;\nINIT x = p;\nTRANS x := x;\n'
        for value in ('TRUE', 'FALSE'):
            r = self.run_query(revision=dict(source=source, root='', inputs={'p': value}))
            self.assertEqual(r['outcome'], 'reachable' if value == 'TRUE' else 'unreachable')
        source = 'MODULE first\n#inertial VAR x : boolean;\nINIT !x;\nTRANS x := x;\nMODULE second\n#inertial VAR x : boolean;\nINIT x;\nTRANS x := x;\n'
        for root in ('first', 'second'):
            r = self.run_query(revision=dict(source=source, root=root, inputs={}))
            self.assertEqual(r['outcome'], 'unreachable' if root == 'first' else 'reachable')

    def test_workbench_named_property_persistence_and_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine(directory, reuse_models=True)
            try:
                rev = engine.save_revision(dict(source=TOGGLE, properties={'never x': '!x'}))
                job = dict(version=1, request_id='safety', revision=rev['id'], query=dict(operation='prove-property', property='never x', limits={'depth': 2}))
                engine.submit(job)
                while engine.job('safety')['running']:
                    time.sleep(.02)
                result = engine.job('safety')['result']
                self.assertEqual(result['outcome'], 'violated', result)
                self.assertTrue(result['trace_validated'])
                self.assertEqual(engine.trace(result['trace_id'])['trace']['query']['property']['name'], 'never x')
                bad = dict(job, request_id='bad', query=dict(job['query'], property='unknown'))
                with self.assertRaises(ValueError): engine.submit(bad)
            finally:
                engine.close()
            reopened = Engine(directory, reuse_models=True)
            try:
                self.assertEqual(reopened.job('safety')['result'], result)
            finally: reopened.close()


if __name__ == '__main__':
    unittest.main()
