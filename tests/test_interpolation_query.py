#!/usr/bin/env python3
"""Interpolation query integration, evidence, replay, and session contracts."""
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.workbench.sessions import Session
from tools.workbench.engine import Engine
from tools.workbench import protocol
def model(edges):
    expression = str(edges[-1])
    for state in reversed(range(len(edges) - 1)):
        expression = f'x = {state} ? {edges[state]} : ({expression})'
    return f'#word-width 2\nMODULE main\n#inertial\nVAR x : uint2;\nINIT x = 0;\nTRANS x := ({expression});\n'



class InterpolationQueries(unittest.TestCase):
    def session(self, source, root='', inputs=None):
        session = Session(str(ROOT / 'yasmv'), str(ROOT), dict(source=source, root=root, inputs=inputs or {}),
                          threading.Event(), time.monotonic() + 90)
        self.addCleanup(session.close)
        return session

    def query(self, session, query, status='completed'):
        result = session.query(dict(query, request_id='interpolation'), threading.Event(), time.monotonic() + 90)
        self.assertEqual(result['status'], status, result)
        return result

    def replay(self, session, result):
        self.assertEqual(self.query(session, dict(operation='validate-trace', trace=result['trace']))['outcome'], 'valid')

    def check_invariant(self, result, edges, bad, initial=0):
        proof = result['proof']
        self.assertTrue(proof['verified'])
        self.assertEqual(proof['verification'], 'fresh-solvers')
        self.assertEqual(set(proof['obligations'].values()), {'unsatisfiable'})
        artifact = proof['invariant']
        self.assertEqual(artifact['identity'], result['identity'])
        self.assertEqual(artifact['assumptions'], proof['assumptions'])
        self.assertEqual(artifact['format'], 'yasmv-state-invariant')
        bits = {entry['atom']: entry for entry in artifact['bits']}
        self.assertEqual(len(bits), len(artifact['bits']))
        def evaluate(state):
            values = {0: False}
            def edge(ref):
                return values[ref & ~1] != bool(ref & 1)
            for node in artifact['nodes']:
                self.assertNotIn(node['id'], values)
                if 'atom' in node:
                    bit = bits[node['atom']]
                    self.assertEqual(bit['symbol'], 'x')
                    self.assertFalse(bit['frozen'])
                    # Native uint2 coordinates are most-significant bit first.
                    values[node['id']] = bool(state & (1 << (1 - bit['bit'])))
                else:
                    self.assertTrue(all((ref & ~1) < node['id'] for ref in node['and']))
                    values[node['id']] = all(edge(ref) for ref in node['and'])
            return edge(artifact['root'])
        self.assertTrue(evaluate(initial))
        self.assertFalse(evaluate(bad))
        for state, successor in enumerate(edges):
            if evaluate(state): self.assertTrue(evaluate(successor))

    def test_graph_outcomes_shortest_paths_invariants_and_depth_caps(self):
        for edges in ([1, 2, 3, 0], [0, 1, 2, 3], [1, 2, 2, 3], [0, 2, 3, 3]):
            session = self.session(model(edges))
            distances = {}; state = 0
            while state not in distances:
                distances[state] = len(distances); state = edges[state]
            for bad in range(4):
                result = self.query(session, dict(operation='reach', strategy='interpolation', target=f'x = {bad}'))
                self.assertEqual(result['strategy'], 'interpolation')
                self.assertEqual(result['scope'], 'unbounded')
                self.assertEqual(result['checked_depths'], list(range(len(result['checked_depths']))))
                if bad in distances:
                    self.assertEqual(result['outcome'], 'reachable')
                    self.assertEqual(result['optimality']['depth'], distances[bad])
                    self.assertEqual(result['checked_depths'], list(range(distances[bad] + 1)))
                    self.assertEqual(result['optimality']['unsat_depths'], list(range(distances[bad])))
                    self.replay(session, result)
                else:
                    self.assertEqual(result['outcome'], 'unreachable')
                    self.check_invariant(result, edges, bad)
                for depth in (1, 3):
                    result = self.query(session, dict(operation='prove-property', strategy='interpolation',
                        property=dict(name='safe', expression=f'x != {bad}'), limits=dict(depth=depth)))
                    if result['outcome'] == 'proven':
                        self.assertNotIn(bad, distances)
                        self.check_invariant(result, edges, bad)
                    elif result['outcome'] == 'violated':
                        self.assertLessEqual(distances[bad], depth)
                        self.assertEqual(result['optimality']['depth'], distances[bad])
                        self.replay(session, result)
                    else:
                        self.assertEqual(result['outcome'], 'holds_bounded')
                        self.assertEqual(result['scope'], 'through_depth')
                        self.assertEqual(result['unbounded_outcome'], 'unknown')
                        self.assertEqual(result['stop_reason'], 'depth_limit')
                        self.assertEqual(result['checked_depths'], list(range(depth + 1)))
                        self.assertEqual(result['proof']['base_unsat_depths'], list(range(depth + 1)))
                        self.assertFalse(result['proof'].get('verified', False))
                        self.assertNotIn('invariant', result['proof'])
            session.close()

    def test_native_types_domains_assumptions_and_empty_initial_states(self):
        source = (ROOT / 'tests/models/interpolation-search.smv').read_text()
        session = self.session(source, root='main', inputs={'gate': 'x'})
        for target in ('n = 3', 'n = 2 && cells[1]', 'gate'):
            result = self.query(session, dict(operation='reach', strategy='interpolation', target=target))
            self.assertEqual(result['outcome'], 'reachable'); self.replay(session, result)
            for frame in result['trace']['steps']:
                self.assertEqual(frame['values']['fixed_bit'], result['trace']['steps'][0]['values']['fixed_bit'])
        for target in ('sub.flag != fixed_bit', '!(palette[0] = RED || palette[0] = GREEN || palette[0] = BLUE)'):
            result = self.query(session, dict(operation='reach', strategy='interpolation', target=target))
            self.assertTrue(result['proof']['verified'])
            self.assertTrue(any(bit['frozen'] for bit in result['proof']['invariant']['bits']))
        for assumption, vacuous in [('n < 2', False), ('n = 7', True)]:
            result = self.query(session, dict(operation='reach', strategy='interpolation', target='n = 2', assumptions=[assumption]))
            self.assertEqual(result['outcome'], 'unreachable')
            self.assertEqual(result['proof']['vacuous'], vacuous)
            self.assertEqual(result['proof']['invariant']['assumptions'], result['proof']['assumptions'])
        for target in ('future', 'view.value', 'choice'):
            result = self.query(session, dict(operation='reach', strategy='interpolation', target=target), 'error')
            self.assertIsNone(result['proof']); self.assertIsNone(result['trace'])

    def test_effective_input_values_are_decoded_and_replayed(self):
        source = """#word-width 3
MODULE main
#inertial VAR x : uint3;
#input VAR number : uint3;
#input VAR signed_number : int3;
#input VAR flags : boolean[2];
#input VAR color : {RED, GREEN, BLUE};
INIT x = 0;
TRANS x := x + 1;
"""
        session = self.session(source, inputs={'number': 'x + 1', 'signed_number': '(int3) x - 1',
                                              'flags': '[x = 0, x = 1]', 'color': 'GREEN'})
        result = self.query(session, dict(operation='reach', strategy='interpolation', target='x = 2'))
        self.assertEqual(result['outcome'], 'reachable')
        self.assertEqual([s['values']['number'] for s in result['trace']['steps']], ['1', '2', '3'])
        self.assertEqual([s['values']['signed_number'] for s in result['trace']['steps']], ['-1', '0', '1'])
        self.assertEqual([s['values']['flags'] for s in result['trace']['steps']], [[True, False], [False, True], [False, False]])
        self.replay(session, result)

    def test_strategy_validation_and_budgets_preserve_session(self):
        session = self.session(model([1, 2, 2, 3]))
        for query in (
            dict(operation='reach', target='x = 2', limits=dict(depth=2)),
            dict(operation='shortest-reach', target='x = 2', limits=dict(depth=2)),
            dict(operation='check-property', property=dict(name='p', expression='TRUE'), limits=dict(depth=2)),
            dict(operation='prove-property', property=dict(name='p', expression='TRUE'), limits=dict(depth=0)),
            dict(operation='check-init')):
            self.query(session, dict(query, strategy='interpolation'), 'error')
        for budget in ('wall_ms', 'conflicts', 'propagations'):
            result = self.query(session, dict(operation='reach', target='x = 3', strategy='interpolation', limits={budget: 0}), 'unknown')
            for field in ('trace', 'proof', 'optimality'): self.assertIsNone(result[field])
        result = self.query(session, dict(operation='reach', target='x = 2', strategy='interpolation'))
        self.replay(session, result)
        ordinary = self.query(session, dict(operation='reach', target='x = 2', limits=dict(depth=1)))
        self.assertEqual(ordinary['scope'], 'through_depth')
        self.assertEqual(ordinary['outcome'], 'unreachable')

    def test_workbench_replay_and_persistent_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine(directory, reuse_models=True)
            try:
                revision = engine.save_revision(dict(source=model([1, 2, 2, 3]), properties={'safe': 'x != 3'}))
                for identifier, query in [('proof', dict(operation='prove-property', property='safe', limits=dict(depth=3))),
                                          ('path', dict(operation='reach', target='x = 2', limits=dict(wall_ms=10000)))]:
                    query['strategy'] = 'interpolation'
                    request = dict(version=1, request_id=identifier, revision=revision['id'], query=query)
                    protocol.request(request)
                    engine.submit(request)
                    deadline = time.monotonic() + 60
                    while engine.job(identifier)['running'] and time.monotonic() < deadline: time.sleep(.02)
                    result = engine.job(identifier)['result']
                    self.assertEqual(result['status'], 'completed', result)
                    if identifier == 'proof': self.assertTrue(result['proof']['verified'])
                    else: self.assertTrue(result['trace_validated'])
            finally: engine.close()
            reopened = Engine(directory, reuse_models=True)
            try:
                proof = reopened.job('proof')['result']
                self.check_invariant(proof, [1, 2, 2, 3], 3)
            finally: reopened.close()

    def test_schema_and_fresh_process_contracts(self):
        try:
            import jsonschema
        except ImportError:
            self.skipTest('optional jsonschema is not installed')
        schemas = {p.name: json.loads(p.read_text()) for p in (ROOT / 'docs/formats').glob('*.schema.json')}
        def validate(name, value):
            schema = schemas[name]
            jsonschema.Draft202012Validator(schema, resolver=jsonschema.RefResolver(
                base_uri=(ROOT / 'docs/formats').as_uri() + '/', referrer=schema,
                store={(ROOT / 'docs/formats' / key).as_uri(): val for key, val in schemas.items()})).validate(value)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory); (path / 'model.smv').write_text(model([1, 2, 2, 3]))
            for target in ('x = 3', 'x = 2'):
                request = dict(version=1, model=str(path / 'model.smv'), query=dict(operation='reach', strategy='interpolation', target=target))
                validate('query-v1.schema.json', request)
                (path / 'request.json').write_text(json.dumps(request))
                run = subprocess.run([str(ROOT / 'yasmv'), '--quiet', '--query-file', str(path / 'request.json')],
                    text=True, capture_output=True, timeout=60, env=dict(os.environ, YASMV_HOME=str(ROOT)))
                self.assertEqual(run.returncode, 0, run.stderr + run.stdout)
                result = json.loads(run.stdout); validate('analysis-v1.schema.json', result)
                if result['proof']:
                    validate('invariant-v1.schema.json', result['proof']['invariant'])
                    damaged = deepcopy(result); del damaged['proof']['obligations']['transition_closure']
                    with self.assertRaises(jsonschema.ValidationError): validate('analysis-v1.schema.json', damaged)
                    damaged = deepcopy(result); damaged['status'] = 'unknown'
                    with self.assertRaises(jsonschema.ValidationError): validate('analysis-v1.schema.json', damaged)
                else: validate('trace-v1.schema.json', result['trace'])
                invalid = deepcopy(request); invalid['query']['limits'] = dict(depth=1)
                with self.assertRaises(jsonschema.ValidationError): validate('query-v1.schema.json', invalid)
        query = dict(operation='prove-property', strategy='interpolation', property='safe', limits=dict(depth=2))
        validate('workbench-v1.schema.json', dict(version=1, request_id='schema', revision='a'*64, query=query))
        query = dict(operation='reach', strategy='interpolation', target='x', limits=dict(wall_ms=1000))
        envelope = dict(version=1, request_id='schema', revision='a'*64, query=query)
        validate('workbench-v1.schema.json', envelope); protocol.request(envelope)
        query['limits']['depth'] = 2
        with self.assertRaises(jsonschema.ValidationError): validate('workbench-v1.schema.json', envelope)
        with self.assertRaises(ValueError): protocol.request(envelope)


if __name__ == '__main__': unittest.main()
