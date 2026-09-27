#!/usr/bin/env python3
"""M1 process contracts and trace replay, using independently known tiny models."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ENV = dict(os.environ, YASMV_HOME=str(ROOT))
TOGGLE = (ROOT / 'tests/models/query.smv').read_text()


class QueryTests(unittest.TestCase):
    def job(self, model=TOGGLE, query=None, expected=0, inputs=None, options=()):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / 'model.smv').write_text(model)
            request = {'version': 1, 'model': str(path / 'model.smv'),
                       'query': query or {'operation': 'check-init'}}
            if inputs is not None:
                request['inputs'] = inputs
            (path / 'request.json').write_text(json.dumps(request))
            p = subprocess.run([str(ROOT / 'yasmv'), '--quiet', '--query-file', str(path / 'request.json'), *options],
                               text=True, capture_output=True, env=ENV, timeout=25)
            self.assertEqual(p.returncode, expected, p.stdout + p.stderr)
            value = json.loads(p.stdout)
            self.assertEqual(value['version'], 1)
            return value

    def reach(self, depth=1, **extra):
        return self.job(query=dict(operation='reach', target='x', limits={'depth': depth}, **extra))

    def replay(self, trace, model=TOGGLE, expected=0, **kwargs):
        return self.job(model, {'operation': 'validate-trace', 'trace': trace, **kwargs}, expected)

    def test_bounded_scope_and_depths(self):
        no = self.reach(0)
        self.assertEqual((no['status'], no['outcome'], no['scope']), ('completed', 'unreachable', 'through_depth'))
        self.assertEqual(no['checked_depths'], [0])
        yes = self.reach(3)
        self.assertEqual(yes['outcome'], 'reachable')
        self.assertEqual(yes['checked_depths'], [0, 1])
        self.assertEqual([f['values']['x'] for f in yes['trace']['steps']], [False, True])
        self.assertEqual(self.replay(yes['trace'])['outcome'], 'valid')

    def test_initial_and_transition_outcomes(self):
        self.assertEqual(self.job()['outcome'], 'satisfiable')
        self.assertEqual(self.job(query={'operation': 'check-init', 'assumptions': ['x']})['outcome'], 'unsatisfiable')
        self.assertEqual(self.job(query={'operation': 'check-trans', 'limits': {'depth': 3}})['checked_depths'], [1, 2, 3])
        self.assertEqual(self.job(query={'operation': 'pick-state', 'count': True})['value'], '1')

    def test_limits_and_cancellation_are_inconclusive(self):
        for limit in ('wall_ms', 'conflicts', 'propagations'):
            with self.subTest(limit=limit):
                r = self.job(query={'operation': 'reach', 'target': 'x', 'limits': {'depth': 2, limit: 0}}, expected=3)
                self.assertEqual(r['status'], 'unknown')
                self.assertIsNone(r['outcome'])
                self.assertIsNone(r['trace'])
        self.assertEqual(self.reach()['outcome'], 'reachable')

    def test_invalid_requests(self):
        for q in ({'operation': 'reach'}, {'operation': 'reach', 'target': 'x', 'strategy': ''},
                  {'operation': 'reach', 'target': 'x ignored'},
                  {'operation': 'reach', 'target': 'next(x)', 'limits': {'depth': 1}},
                  {'operation': 'reach', 'target': 'x', 'limits': {'depth': -2}},
                  {'operation': 'reach', 'target': 'x', 'limits': {'depth': 2}, 'assumptions': ['$0{x}']},
                  {'operation': 'check-init', 'typo': 1}):
            with self.subTest(q=q):
                self.assertEqual(self.job(query=q, expected=2)['status'], 'error')

    def test_timed_goal_hidden_in_define_is_rejected(self):
        model = TOGGLE + 'DEFINE later := next(x);\n'
        self.job(model, {'operation': 'reach', 'target': 'later', 'limits': {'depth': 1}}, expected=2)

    def test_distinct_source_occurrences(self):
        records = [c for c in self.job()['constraints'] if c['kind'] == 'invar' and c['span']]
        self.assertEqual(len(records), 2)
        self.assertNotEqual(records[0]['id'], records[1]['id'])
        self.assertEqual([r['span']['line'] for r in records], [5, 6])

    def test_guard_diagnostics_and_generated_parentage(self):
        head = 'MODULE main\n#inertial\nVAR x:boolean;\n'
        bad = self.job(head + 'TRANS TRUE ?: x:=TRUE;\nTRANS TRUE ?: x:=FALSE;\n', expected=2)
        conflict = next(d for d in bad['diagnostics'] if d['code'] == 'guard-conflict')
        self.assertEqual({conflict['primary']['line'], *[s['line'] for s in conflict['related']]}, {4, 5})
        good = self.job(head + 'TRANS x ?: x:=FALSE;\n')
        generated = next(c for c in good['constraints'] if c['explanation'].startswith('Preserve'))
        self.assertIsNone(generated['span'])
        self.assertGreaterEqual(len(generated['parents']), 2)

    def test_validation_diagnostic_spans(self):
        r = self.job('MODULE main\nVAR x:boolean;\nINIT missing;\n', expected=2)
        self.assertTrue(any(d['primary'] and d['primary']['line'] == 3 for d in r['diagnostics']))

    def test_tampered_trace_and_missing_values(self):
        t = self.reach()['trace']
        bad = copy.deepcopy(t); bad['steps'][1]['values']['x'] = False
        r = self.replay(bad)
        self.assertEqual(r['outcome'], 'invalid')
        self.assertIn('step 1', r['diagnostics'][0]['message'])
        bad = copy.deepcopy(t); bad['identity']['model_revision'] = 'wrong'
        self.replay(bad, expected=2)
        bad = copy.deepcopy(t); bad['steps'][0]['values']['x'] = None
        self.assertEqual(self.replay(bad, expected=3)['status'], 'unknown')
        bad = copy.deepcopy(t); bad['steps'][1]['step'] = 7
        self.replay(bad, expected=2)
        bad = copy.deepcopy(t); bad['version'] = 2
        self.replay(bad, expected=2)
        bad = copy.deepcopy(t); bad['steps'][0]['values']['x'] = 'false'
        self.replay(bad, expected=2)

    def test_query_goal_and_assumptions_replayed(self):
        t = self.reach()['trace']
        t['query']['target'] = '!x'
        self.replay(t, expected=2)
        t = self.reach()['trace']; t['query']['assumptions'] = ['!x']
        self.assertEqual(self.replay(t)['outcome'], 'invalid')

    def test_exact_integer_array_enum_roundtrip(self):
        model = ('#word-width 64\nMODULE main\nVAR u:uint64; s:int64; a:boolean[2]; b:uint64[2]; e:{RED,GREEN,BLUE};\n'
                 'INIT u=(uint64)18446744073709551615 && s=(int64)-9223372036854775808;\n'
                 'INIT a=[TRUE,FALSE] && e=GREEN;\nINIT b=[(uint64)0,(uint64)18446744073709551615];\n')
        r = self.job(model, {'operation': 'pick-state'})
        t = r['trace']; values = t['steps'][0]['values']
        self.assertEqual(values['u'], '18446744073709551615')
        self.assertEqual(values['s'], '-9223372036854775808')
        self.assertEqual(values['a'], [True, False])
        self.assertEqual(values['e'], 'GREEN')
        self.assertEqual(values['b'], ['0', '18446744073709551615'])
        self.assertEqual(self.replay(t, model)['outcome'], 'valid')
        goal = self.job(model, {'operation': 'reach', 'target': 's=(int64)-9223372036854775808', 'limits': {'depth': 0}})['trace']
        self.assertEqual(self.replay(goal, model)['outcome'], 'valid')
        for value in ('18446744073709551616', '-1', 9007199254740993):
            bad = copy.deepcopy(t); bad['steps'][0]['values']['u'] = value
            self.replay(bad, model, expected=2)

    def test_mixed_width_integer_trace_replay(self):
        model = ('#word-width 64\nMODULE main\n#inertial\nVAR u:uint8; s:int16; a:uint8[2];\n'
                 'INIT u=(uint8)255 && s=(int16)-32768;\n'
                 'INIT a=[(uint8)0,(uint8)255];\n'
                 'TRANS TRUE ?: u:=u, s:=s, a:=a;\n')
        trace = self.job(model, {'operation': 'pick-state'})['trace']
        self.assertEqual(self.replay(trace, model)['outcome'], 'valid')
        continuation = self.job(model, {'operation': 'simulate', 'trace': trace, 'limits': {'depth': 1}})['trace']
        self.assertEqual(self.replay(continuation, model)['outcome'], 'valid')
        bad = copy.deepcopy(continuation); bad['steps'][1]['values']['a'][1] = '254'
        self.assertEqual(self.replay(bad, model)['outcome'], 'invalid')

    def test_backward_trace(self):
        r = self.job(query={'operation': 'reach', 'target': 'x', 'assumptions': ['$0{x}']})
        self.assertEqual(r['outcome'], 'reachable')
        self.assertEqual(r['trace']['origin']['initial_time'], 4294967294)
        self.assertEqual(self.replay(r['trace'])['outcome'], 'valid')

    def test_frozen_values(self):
        model = 'MODULE main\n#frozen\nVAR f:boolean;\n#inertial\nVAR x:boolean;\nINIT f && !x;\nTRANS x:=!x;\n'
        t = self.job(model, {'operation': 'reach', 'target': 'x', 'limits': {'depth': 1}})['trace']
        self.assertEqual([f['values']['f'] for f in t['steps']], [True, True])
        self.assertEqual(self.replay(t, model)['outcome'], 'valid')

    def test_continuation_branch_and_deadlock(self):
        parent = self.reach()['trace']
        r = self.job(query={'operation': 'simulate', 'trace': parent, 'limits': {'depth': 2}})
        self.assertEqual(r['outcome'], 'simulated')
        child = r['trace']
        self.assertEqual(child['steps'][:2], parent['steps'])
        self.assertEqual([f['values']['x'] for f in child['steps']], [False, True, False, True])
        self.assertEqual(self.replay(child)['outcome'], 'valid')
        grandchild = self.job(query={'operation': 'simulate', 'trace': child})['trace']
        self.assertEqual(self.replay(grandchild)['outcome'], 'valid')
        r = self.job(query={'operation': 'simulate', 'trace': parent, 'assumptions': ['!x']})
        self.assertEqual(r['outcome'], 'deadlocked')
        self.assertEqual(self.replay(r['trace'])['outcome'], 'valid')
        bad = copy.deepcopy(child); bad['steps'][0]['values']['x'] = True
        self.replay(bad, expected=2)

    def test_diameter_and_unbounded_proof(self):
        r = self.job(query={'operation': 'diameter'})
        self.assertEqual((r['outcome'], r['value']), ('diameter', '1'))
        r = self.job(query={'operation': 'diameter', 'limits': {'depth': 0}}, expected=3)
        self.assertEqual(r['stop_reason'], 'depth_limit')
        r = self.job(query={'operation': 'reach', 'target': 'FALSE'})
        self.assertEqual((r['outcome'], r['scope']), ('unreachable', 'unbounded'))
        self.assertTrue(r['proof_method'])

    def test_parameter_provenance_and_root(self):
        model = 'MODULE child(p:boolean)\nVAR x:boolean;\nINIT x=p;\nMODULE main\nVAR a:child(TRUE); b:child(FALSE);\n'
        r = self.job(model, {'operation': 'pick-state'}, options=('--root', 'main'))
        instances = [c for c in r['constraints'] if '@' in c['id']]
        self.assertGreaterEqual(len(instances), 2)
        self.assertTrue(all(c['parents'] for c in instances))
        self.assertEqual(r['trace']['steps'][0]['values'], {'a.x': True, 'b.x': False})
        self.assertEqual(self.job(model, {'operation': 'validate-trace', 'trace': r['trace']}, options=('--root', 'main'))['outcome'], 'valid')

    def test_input_identity(self):
        model = 'MODULE main\n#input\nVAR enabled:boolean;\nVAR x:boolean;\nINIT x=enabled;\n'
        r = self.job(model, {'operation': 'pick-state'}, inputs={'enabled': 'TRUE'})
        self.assertEqual(r['trace']['steps'][0]['values'], {'enabled': True, 'x': True})
        self.assertEqual(self.job(model, {'operation': 'validate-trace', 'trace': r['trace']}, inputs={'enabled': 'TRUE'})['outcome'], 'valid')
        self.job(model, {'operation': 'validate-trace', 'trace': r['trace']}, inputs={'enabled': 'FALSE'}, expected=2)

    def test_negative_input_values(self):
        model = 'MODULE main\n#input\nVAR n:int16;\nVAR x:int16;\nINIT x=n;\n'
        r = self.job(model, {'operation': 'pick-state'}, inputs={'n': '-7'})
        self.assertEqual(r['trace']['steps'][0]['values'], {'n': '-7', 'x': '-7'})
        self.assertEqual(self.job(model, {'operation': 'validate-trace', 'trace': r['trace']}, inputs={'n': '-7'})['outcome'], 'valid')

    def test_cli_and_machine_agree(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            model = path/'model.smv'; model.write_text(TOGGLE)
            output = path/'trace.json'
            commands = f'read-model "{model}"\npick-state\nsimulate -k 2\ndump-trace -f json -o "{output}"\nquit\n'
            p = subprocess.run([str(ROOT/'yasmv'), '--quiet'], input=commands, text=True, capture_output=True, env=ENV, timeout=25)
            self.assertEqual(p.returncode, 0, p.stdout+p.stderr)
            artifact = json.loads(output.read_text())
            self.assertEqual([f['values']['x'] for f in artifact['steps']], [False, True, False])
            self.assertEqual(self.replay(artifact)['outcome'], 'valid')
            imported = path/'imported.json'
            commands = f'read-trace "{output}"\ndump-trace -f json -o "{imported}"\nquit\n'
            p = subprocess.run([str(ROOT/'yasmv'), '--quiet', str(model)], input=commands, text=True, capture_output=True, env=ENV, timeout=25)
            self.assertEqual(p.returncode, 0, p.stdout+p.stderr)
            self.assertEqual(json.loads(imported.read_text()), artifact)

    def test_json_number_normalization_preserves_branch_identity(self):
        def normalize(value):
            if isinstance(value, dict):
                return {k: normalize(v) for k, v in value.items()}
            if isinstance(value, list):
                return [normalize(v) for v in value]
            if isinstance(value, float) and value.is_integer():
                return int(value)
            return value
        parent = normalize(self.reach()['trace'])
        self.assertEqual(self.replay(parent)['outcome'], 'valid')
        child = normalize(self.job(query={'operation': 'simulate', 'trace': parent})['trace'])
        self.assertEqual(self.replay(child)['outcome'], 'valid')

    def test_runner_hard_deadline_discards_partial_output(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path/'request.json').write_text(json.dumps({'version': 1, 'query': {'request_id': 'deadline'}}))
            checker = path/'checker'; checker.write_text('#!/bin/sh\ntrap "" TERM\necho partial\nsleep 2\n')
            checker.chmod(0o755)
            p = subprocess.run(['python3', str(ROOT/'tools/run-query.py'), str(path/'request.json'),
                                '--binary', str(checker), '--hard-timeout', '0.05'], capture_output=True, text=True, timeout=5)
            self.assertEqual(p.returncode, 3)
            r = json.loads(p.stdout)
            self.assertTrue(r['forced_termination'])
            self.assertIsNone(r['trace'])


if __name__ == '__main__':
    unittest.main()
