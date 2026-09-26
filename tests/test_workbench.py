#!/usr/bin/env python3
"""M2 artifact, isolation, protocol, and independent retry-model acceptance gates."""
from copy import deepcopy
import importlib.util
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
from urllib.error import HTTPError
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.workbench.engine import Engine, atomic
from tools.workbench import protocol
from tools.workbench.server import make_server

spec = importlib.util.spec_from_file_location('retry_runner', ROOT / 'examples/retry-protocol/runner.py')
retry = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = retry
spec.loader.exec_module(retry)
TOGGLE = (ROOT / 'tests/models/query.smv').read_text()


class WorkbenchTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.engine = Engine(Path(self.temp.name) / 'store')
        self.counter = 0

    def tearDown(self):
        self.engine.close()
        self.temp.cleanup()

    def revision(self, source=TOGGLE, **extra):
        return self.engine.save_revision(dict(source=source, **extra))

    def request(self, rev, query, **extra):
        self.counter += 1
        return dict(version=1, request_id=f'job-{self.counter}', revision=rev['id'], query=query, **extra)

    def wait(self, identifier):
        end = time.monotonic() + 90
        while self.engine.job(identifier)['running']:
            self.assertLess(time.monotonic(), end)
            time.sleep(.05)
        events = self.engine.events(identifier)
        self.assertEqual(events[0]['event'], 'started')
        self.assertEqual([e['seq'] for e in events], list(range(len(events))))
        self.assertEqual(sum(e['event'] == 'result' for e in events), 1)
        result = self.engine.job(identifier)['result']
        self.assertEqual(events[-1]['result'], result)
        self.assertEqual(result['request_id'], identifier)
        return result

    def run_job(self, rev, query, **extra):
        return self.wait(self.engine.submit(self.request(rev, query, **extra)))

    def reach(self, rev, target='x', depth=2):
        return self.run_job(rev, dict(operation='reach', target=target, limits={'depth': depth}))

    def fake(self, code):
        path = Path(self.temp.name) / 'fake-worker'
        path.write_text('#!/usr/bin/env python3\n' + code)
        path.chmod(0o700)
        self.engine.binary = str(path)

    def test_revision_identity_and_immutability(self):
        a = self.revision(inputs={'i': '0'})
        self.assertEqual(a, self.revision(inputs={'i': '0'}))
        b = self.revision(inputs={'i': '1'})
        self.assertNotEqual(a['id'], b['id'])
        self.assertNotEqual(a['id'], self.revision(source=TOGGLE + '\n')['id'])
        self.assertEqual(self.engine.revision(a['id'])['inputs'], {'i': '0'})
        self.assertEqual(len(self.engine.revisions()), 3)

    def test_malformed_protocol_never_launches_worker(self):
        rev = self.revision()
        marker = Path(self.temp.name) / 'launched'
        self.fake(f'from pathlib import Path\nPath({str(marker)!r}).touch()\n')
        base = self.request(rev, {'operation': 'reach', 'target': 'x', 'limits': {'depth': 2}})
        variants = []
        for key, value in [('version', 2), ('version', True), ('extra', 1), ('request_id', '../escape')]:
            v = deepcopy(base); v[key] = value; variants.append(v)
        for query in [{'operation': 'arbitrary'}, {'operation': 'reach', 'target': 'x'},
                      {'operation': 'pick-state', 'limits': {'depth': 1}},
                      {'operation': 'reach', 'target': 'x', 'limits': {'depth': True}},
                      {'operation': 'reach', 'target': 'x', 'limits': {'depth': -1}},
                      {'operation': 'simulate', 'trace': {}, 'trace_id': 'x', 'limits': {'depth': 1}},
                      {'operation': 'validate-model', 'assumptions': ['x']}]:
            v = deepcopy(base); v['query'] = query; variants.append(v)
        for v in variants:
            with self.subTest(request=v), self.assertRaises(ValueError): self.engine.submit(v)
        self.assertFalse(marker.exists())
        self.assertEqual(self.engine.jobs(), [])
        for text in ['{"a":1,"a":2}', '{"a":NaN}', '{"a":1e999}', '[' * 2000 + '0' + ']' * 2000]:
            with self.assertRaises(ValueError): protocol.loads(text)

    def test_concurrent_revisions_and_inputs_are_isolated(self):
        source = '#word-width 4\nMODULE main\n#input\nVAR i : boolean;\n#inertial\nVAR x : boolean;\nINIT x = i;\n'
        left = self.revision(source, inputs={'i': 'FALSE'})
        right = self.revision(source, inputs={'i': 'TRUE'})
        jobs = [self.engine.submit(self.request(rev, {'operation': 'pick-state'})) for rev in (left, right)]
        results = list(map(self.wait, jobs))
        self.assertEqual([r['status'] for r in results], ['completed', 'completed'], results)
        self.assertEqual([r['trace']['steps'][0]['values']['x'] for r in results], [False, True])
        self.assertNotEqual(results[0]['identity'], results[1]['identity'])
        self.assertTrue(all(r['trace_validated'] for r in results))

    def test_model_validation_and_diagnostics(self):
        no_initial = self.revision('MODULE main\nVAR x : boolean;\nINIT x;\nINIT !x;\n')
        valid = self.run_job(no_initial, {'operation': 'validate-model'})
        self.assertEqual((valid['outcome'], valid['scope']), ('valid', 'model'))
        self.assertEqual(self.run_job(no_initial, {'operation': 'pick-state'})['outcome'], 'unsatisfiable')
        broken = self.revision('MODULE main\nVAR x : boolean;\nINIT missing;\n')
        invalid = self.run_job(broken, {'operation': 'validate-model'})
        self.assertEqual(invalid['status'], 'error')
        self.assertTrue(invalid['diagnostics'])

    def test_prefix_branch_parent_replay_watches_and_persistence(self):
        rev = self.revision(watches={'enabled': 'x'})
        parent = self.reach(rev)
        self.assertEqual(parent['watches']['enabled'], [False, True])
        saved = deepcopy(parent['trace'])
        child = self.run_job(rev, dict(operation='simulate', trace_id=parent['trace_id'], prefix_length=1, limits={'depth': 3}))
        self.assertEqual(child['status'], 'completed', child)
        self.assertTrue(child['trace_validated'])
        self.assertEqual(child['trace']['branch']['prefix_length'], 1)
        self.assertEqual(child['trace']['steps'][0], saved['steps'][0])
        self.assertEqual(child['watches']['enabled'], [False, True, False, True])
        self.assertEqual(self.engine.trace(parent['trace_id'])['trace'], saved)
        self.engine.close(); self.engine = Engine(Path(self.temp.name) / 'store')
        self.assertEqual(self.engine.trace(child['trace_id'])['trace'], child['trace'])
        self.assertEqual(len(self.engine.traces()), 2)
        replay = self.run_job(rev, dict(operation='validate-trace', trace=child['trace']))
        self.assertEqual(replay['outcome'], 'valid')
        self.assertEqual(len(self.engine.traces()), 2)

    def test_watch_overrides_are_reproducible_artifacts(self):
        rev = self.revision(watches={'enabled': 'x'})
        parent = self.reach(rev)
        result = self.run_job(rev, dict(operation='validate-trace', trace=parent['trace'], watches={'enabled': '!x'}))
        self.assertEqual(result['watches']['enabled'], [True, False])
        self.assertNotEqual(parent['trace_id'], result['trace_id'])
        artifact = self.engine.trace(result['trace_id'])
        self.assertEqual(artifact['watches'], result['watches'])
        self.assertEqual(artifact['watch_expressions'], {'enabled': '!x'})
        self.assertEqual(self.engine.trace(parent['trace_id'])['watches']['enabled'], [False, True])

    def test_blocked_prefix_retains_only_selected_prefix(self):
        rev = self.revision()
        parent = self.reach(rev)
        child = self.run_job(rev, dict(operation='simulate', trace_id=parent['trace_id'], prefix_length=1,
                                      assumptions=['x'], limits={'depth': 2}))
        self.assertEqual(child['outcome'], 'deadlocked', child)
        self.assertEqual(len(child['trace']['steps']), 1)
        self.assertTrue(child['trace_validated'])
        self.assertEqual(child['trace']['steps'], parent['trace']['steps'][:1])
        invalid = self.run_job(rev, dict(operation='simulate', trace_id=parent['trace_id'], prefix_length=99, limits={'depth': 1}))
        self.assertEqual(invalid['status'], 'error')

    def test_untrusted_and_wrong_revision_imports(self):
        rev = self.revision()
        parent = self.reach(rev)
        damaged = deepcopy(parent['trace']); damaged['steps'][1]['values']['x'] = False
        result = self.run_job(rev, dict(operation='validate-trace', trace=damaged))
        self.assertNotIn('trace_id', result)
        other = self.revision(TOGGLE.replace('INIT !x', 'INIT x'))
        with self.assertRaises(ValueError):
            self.engine.submit(self.request(other, dict(operation='simulate', trace_id=parent['trace_id'], limits={'depth': 1})))
        result = self.run_job(other, dict(operation='validate-trace', trace=parent['trace']))
        self.assertEqual(result['status'], 'error')
        self.assertEqual(len(self.engine.traces()), 1)

    def test_watches_reject_temporal_and_nonboolean_expressions(self):
        for watch in ['next(x)', '1']:
            result = self.reach(self.revision(watches={'bad': watch}))
            self.assertEqual(result['status'], 'error')
            self.assertIsNone(result['trace'])

    def test_crash_and_malformed_output_preserve_revision(self):
        rev = self.revision()
        for code in ['import os,signal\nos.kill(os.getpid(), signal.SIGKILL)\n', 'print("not JSON")\n']:
            self.fake(code)
            result = self.run_job(rev, {'operation': 'validate-model'})
            self.assertEqual((result['status'], result['stop_reason']), ('error', 'worker_failed'))
            self.assertEqual(self.engine.revision(rev['id']), rev)
        self.assertEqual(self.engine.traces(), [])

    def test_cancel_and_deadline_kill_workers(self):
        self.fake('import os,time\nfrom pathlib import Path\nPath("pid").write_text(str(os.getpid()))\ntime.sleep(90)\n')
        rev = self.revision()
        identifier = self.engine.submit(self.request(rev, {'operation': 'validate-model'}))
        directory = self.engine.path('jobs', identifier)
        end = time.monotonic() + 5
        while not (directory / 'pid').exists():
            self.assertLess(time.monotonic(), end); time.sleep(.02)
        pid = int((directory / 'pid').read_text())
        self.assertTrue(self.engine.cancel(identifier))
        result = self.wait(identifier)
        self.assertEqual((result['status'], result['stop_reason']), ('unknown', 'cancelled'))
        with self.assertRaises(ProcessLookupError): os.kill(pid, 0)
        result = self.run_job(rev, {'operation': 'validate-model'}, hard_timeout=.1)
        self.assertEqual(result['stop_reason'], 'deadline')
        self.assertFalse(self.engine.cancel(identifier))

    def test_restart_recovers_partial_events_once(self):
        rev = self.revision()
        request = self.request(rev, {'operation': 'validate-model'})
        directory = self.engine.path('jobs', request['request_id']); directory.mkdir()
        atomic(directory / 'request.json', request)
        self.engine.emit(request['request_id'], 'started')
        with (directory / 'events.jsonl').open('ab') as stream: stream.write(b'{"partial":')
        self.engine.close(); self.engine = Engine(Path(self.temp.name) / 'store')
        result = self.wait(request['request_id'])
        self.assertEqual(result['stop_reason'], 'worker_interrupted')
        self.engine.close(); self.engine = Engine(Path(self.temp.name) / 'store')
        self.assertEqual(len(self.engine.events(request['request_id'])), 2)

    def test_cli_json_lines_and_capabilities(self):
        rev = self.revision(); request = self.request(rev, {'operation': 'validate-model'})
        path = Path(self.temp.name) / 'request.json'; path.write_text(json.dumps(request))
        self.engine.close()
        try:
            p = subprocess.run([sys.executable, '-m', 'tools.workbench', '--store', str(Path(self.temp.name) / 'store'), 'run', str(path)], cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
            events = [json.loads(line) for line in p.stdout.splitlines()]
            self.assertEqual([e['event'] for e in events].count('result'), 1)
            self.assertEqual(events[-1]['result']['outcome'], 'valid')
        finally:
            self.engine = Engine(Path(self.temp.name) / 'store')
        caps = subprocess.check_output([sys.executable, '-m', 'tools.workbench', 'capabilities'], cwd=ROOT, text=True)
        self.assertEqual(json.loads(caps), protocol.CAPABILITIES)

    def test_http_transport_and_origin_protection(self):
        server = make_server(self.engine, 0)
        thread = threading.Thread(target=server.serve_forever); thread.start()
        base = f'http://127.0.0.1:{server.server_port}'
        try:
            with urlopen(base + '/') as response:
                self.assertIn(b'Trace timeline', response.read())
                self.assertIn("frame-ancestors 'none'", response.headers['Content-Security-Policy'])
            data = json.dumps({'source': TOGGLE}).encode()
            with urlopen(Request(base + '/api/revisions', data=data, headers={'Content-Type': 'application/json'})) as response:
                self.assertEqual(response.status, 201)
            for headers in [{'Host': 'evil.example'}, {'Origin': 'http://evil.example'}, {'Content-Type': 'text/plain'}]:
                request = Request(base + '/api/revisions', data=data, headers={'Content-Type': 'application/json', **headers})
                with self.assertRaises(HTTPError) as error: urlopen(request)
                self.assertIn(error.exception.code, (400, 403))
            with self.assertRaises(HTTPError) as error: urlopen(base + '/../../etc/passwd')
            self.assertEqual(error.exception.code, 404)
        finally:
            server.shutdown(); thread.join(); server.server_close()

    def test_retry_demo_matches_independent_state_graph(self):
        self.assertEqual(retry.graph(), {'states': 32, 'edges': 44, 'duplicate': ['SEND', 'DELIVER', 'DROP_ACK', 'RETRY', 'DELIVER'], 'max_distance': 10})
        self.assertEqual(retry.graph(True), {'states': 20, 'edges': 28, 'duplicate': None, 'max_distance': 8})
        directory = ROOT / 'examples/retry-protocol'
        rev = self.revision((directory / 'faulty.smv').read_text(), watches={'duplicate': 'DUPLICATE'})
        result = self.reach(rev, 'DUPLICATE', 12)
        self.assertEqual(result['outcome'], 'reachable', result)
        self.assertEqual(result['checked_depths'], list(range(6)))
        frames = result['trace']['steps']
        actions = [f['values']['action'] for f in frames[:-1]]
        self.assertEqual(actions, retry.graph()['duplicate'])
        expected = retry.replay(actions)
        for frame, s in zip(frames, expected):
            values = frame['values']
            self.assertEqual((values['phase'], int(values['retries']), int(values['executions']), values['seen']),
                             (s.phase, s.retries, s.executions, s.seen))
        self.assertEqual(result['watches']['duplicate'], [False] * 5 + [True])
        fixed = self.revision((directory / 'deduplicating.smv').read_text())
        negative = self.reach(fixed, 'DUPLICATE', 12)
        self.assertEqual((negative['outcome'], negative['scope'], negative['unbounded_outcome']), ('unreachable', 'through_depth', 'unknown'))
        self.assertEqual(negative['checked_depths'], list(range(13)))


if __name__ == '__main__':
    unittest.main()
