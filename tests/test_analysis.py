#!/usr/bin/env python3
"""M4: compare certificates and induction with exhaustive finite-state oracles."""
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


def model(edges, initial=0):
    expression = str(edges[-1])
    for state in reversed(range(len(edges) - 1)):
        expression = f'x = {state} ? {edges[state]} : ({expression})'
    return f'#word-width 2\nMODULE main\n#inertial\nVAR x : uint2;\nINIT x = {initial};\nTRANS x := ({expression});\n'


class AnalysisTests(unittest.TestCase):
    def session(self, source):
        session = Session(str(ROOT / 'yasmv'), str(ROOT), dict(source=source, root='', inputs={}), threading.Event(), time.monotonic() + 90)
        self.addCleanup(session.close)
        return session

    def run_query(self, session, query):
        result = session.query(dict(query, request_id='analysis'), threading.Event(), time.monotonic() + 90)
        self.assertNotEqual(result['status'], 'error', result)
        return result

    def test_shortest_against_exhaustive_graphs_and_replay(self):
        for edges in ([1, 2, 3, 0], [0, 1, 2, 3], [1, 2, 2, 3], [0, 2, 3, 3]):
            session = self.session(model(edges))
            distances = {}
            state = 0
            while state not in distances:
                distances[state] = len(distances)
                state = edges[state]
            for goal in range(4):
                with self.subTest(edges=edges, goal=goal):
                    result = self.run_query(session, dict(operation='shortest-reach', target=f'x = {goal}', limits={'depth': 4}))
                    if goal in distances:
                        depth = distances[goal]
                        self.assertEqual(result['outcome'], 'reachable')
                        self.assertEqual(result['optimality']['unsat_depths'], list(range(depth)))
                        self.assertTrue(result['optimality']['certified'])
                        self.assertEqual(len(result['trace']['steps']), depth + 1)
                        replay = self.run_query(session, dict(operation='validate-trace', trace=result['trace']))
                        self.assertEqual(replay['outcome'], 'valid')
                    else:
                        self.assertEqual(result['outcome'], 'unreachable')
                        self.assertEqual(result['unbounded_outcome'], 'unknown')
                        self.assertIsNone(result['optimality'])
            session.close()

    def test_induction_against_exhaustive_graphs(self):
        for edges in ([1, 2, 3, 0], [0, 1, 2, 3], [1, 2, 2, 3], [0, 2, 3, 3]):
            session = self.session(model(edges))
            reachable = set()
            state = 0
            while state not in reachable:
                reachable.add(state); state = edges[state]
            for forbidden in range(4):
                for depth in (1, 3):
                    result = self.run_query(session, dict(operation='prove-property', property={'name': 'safe', 'expression': f'x != {forbidden}'}, limits={'depth': depth}))
                    if result['outcome'] == 'proven':
                        self.assertNotIn(forbidden, reachable)
                        self.assertEqual(result['scope'], 'unbounded')
                        self.assertTrue(result['proof']['verified'])
                        self.assertEqual(result['proof']['verified_base_depths'], list(range(depth + 1)))
                    elif result['outcome'] == 'violated':
                        self.assertIn(forbidden, reachable)
                        self.assertEqual(self.run_query(session, dict(operation='validate-trace', trace=result['trace']))['outcome'], 'valid')
                    else:
                        self.assertEqual(result['outcome'], 'holds_bounded')
                        self.assertEqual(result['unbounded_outcome'], 'unknown')
                        self.assertEqual(result['proof']['step_status'], 'satisfiable')
                        self.assertEqual(result['proof']['induction_counterexample']['reachable'], 'not_established')
                        states = [int(frame['values']['x']) for frame in result['proof']['induction_counterexample']['trace']['steps']]
                        self.assertTrue(all(state != forbidden for state in states[:-1]))
                        self.assertEqual(states[-1], forbidden)
                        self.assertTrue(all(edges[a] == b for a, b in zip(states, states[1:])))
                        self.assertIsNone(result['trace'])
            session.close()

    def test_unreachable_step_assignment_then_three_induction(self):
        session = self.session(model([0, 2, 3, 3]))
        q = dict(operation='prove-property', property={'name': 'safe', 'expression': 'x != 3'}, limits={'depth': 1})
        result = self.run_query(session, q)
        self.assertEqual(result['outcome'], 'holds_bounded')
        step = result['proof']['induction_counterexample']['trace']
        self.assertEqual(step['steps'][0]['values']['x'], '2')
        q['limits']['depth'] = 3
        self.assertEqual(self.run_query(session, q)['outcome'], 'proven')

    def test_assumptions_dead_ends_and_zero_step_refutation(self):
        session = self.session(model([1, 2, 3, 0]))
        q = dict(operation='check-property', property={'name': 'safe', 'expression': 'x != 0'}, limits={'depth': 0})
        result = self.run_query(session, q)
        self.assertEqual(result['outcome'], 'violated')
        self.assertEqual(result['optimality']['unsat_depths'], [])
        tampered = deepcopy(result['trace'])
        tampered['query']['property']['expression'] = 'TRUE'
        replay = session.query(dict(request_id='tampered', operation='validate-trace', trace=tampered), threading.Event(), time.monotonic() + 90)
        self.assertEqual(replay['status'], 'error')
        q.update(operation='prove-property', property={'name': 'safe', 'expression': 'x != 3'}, assumptions=['x < 2'], limits={'depth': 1})
        result = self.run_query(session, q)
        self.assertEqual(result['outcome'], 'proven')
        self.assertEqual(result['proof']['assumptions'], ['(x < 2)'])
        dead = self.session('MODULE main\n#inertial\nVAR x : boolean;\nINIT x;\nINVAR x;\nTRANS x := !x;\n')
        result = self.run_query(dead, dict(operation='prove-property', property={'name': 'safe', 'expression': 'x'}, limits={'depth': 2}))
        self.assertEqual(result['outcome'], 'proven')

    def test_unknown_and_bad_properties_do_not_create_certificates(self):
        session = self.session(model([0, 1, 2, 3]))
        for limit in ('wall_ms', 'conflicts', 'propagations'):
            for op in ('shortest-reach', 'prove-property'):
                q = dict(operation=op, limits={'depth': 3, limit: 0})
                q.update(target='x = 3') if op == 'shortest-reach' else q.update(property={'name': 'safe', 'expression': 'x != 3'})
                result = self.run_query(session, q)
                self.assertEqual(result['status'], 'unknown')
                self.assertIsNone(result['trace'])
                self.assertIsNone(result['optimality'])
                self.assertFalse((result.get('proof') or {}).get('verified'))
        for expression in ('next(x) = 0', 'x + 1', 'missing'):
            result = session.query(dict(request_id='bad', operation='prove-property', property={'name': 'bad', 'expression': expression}, limits={'depth': 1}), threading.Event(), time.monotonic() + 90)
            self.assertEqual(result['status'], 'error', result)
        result = self.run_query(session, dict(operation='shortest-reach', target='x = 0', limits={'depth': 0}))
        self.assertTrue(result['optimality']['certified'])

    def test_retry_protocol_counterexample_and_proof(self):
        for receiver in ('faulty', 'deduplicating'):
            session = self.session((ROOT / f'examples/retry-protocol/{receiver}.smv').read_text())
            q = dict(operation='prove-property', property={'name': 'at most once', 'expression': '!DUPLICATE'}, limits={'depth': 12})
            result = self.run_query(session, q)
            if receiver == 'faulty':
                self.assertEqual(result['outcome'], 'violated')
                self.assertEqual(result['optimality']['depth'], 5)
            else:
                self.assertEqual(result['outcome'], 'proven', result)


if __name__ == '__main__':
    unittest.main()
