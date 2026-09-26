#!/usr/bin/env python3
"""Reassert and delete reported high-level constraints in fresh checker processes."""
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
TOGGLE = (ROOT / 'tests/models/query.smv').read_text()


class ExplanationTests(unittest.TestCase):
    def job(self, model, query, expected=0, options=()):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            (directory / 'model.smv').write_text(model)
            (directory / 'query.json').write_text(json.dumps(dict(version=1, model=str(directory / 'model.smv'), query=query)))
            p = subprocess.run([str(ROOT / 'yasmv'), '--quiet', '--query-file', str(directory / 'query.json'), *options],
                               capture_output=True, text=True, env=dict(os.environ, YASMV_HOME=str(ROOT)), timeout=90)
            self.assertEqual(p.returncode, expected, p.stdout + p.stderr)
            return json.loads(p.stdout)

    def assert_core(self, model, query, result, delete=True, options=()):
        self.assertEqual(result['outcome'], 'unsatisfiable', result)
        for case in result['explanation']['cases']:
            self.assertTrue(case['verified_unsat'])
            q = deepcopy(query)
            core_options = dict(active_ids=[c['id'] for c in case['constraints']])
            if q['operation'] == 'explain-reach':
                q['limits']['depth'] = case['depth']; core_options['exact_depth'] = True
            q['explanation'] = core_options
            self.assertEqual(self.job(model, q, options=options)['outcome'], 'unsatisfiable')
            if delete:
                self.assertTrue(case['subset_minimal'])
                for identifier in core_options['active_ids']:
                    subset = deepcopy(q)
                    subset['explanation']['active_ids'].remove(identifier)
                    self.assertEqual(self.job(model, subset, options=options)['outcome'], 'satisfiable', identifier)

    def test_initial_minimal_core_has_sources(self):
        model = 'MODULE main\nVAR x : boolean;\nVAR y : boolean;\nINIT x;\nINIT !x;\nINIT y;\n'
        q = dict(operation='explain-init', explanation={'minimize': True})
        result = self.job(model, q)
        self.assert_core(model, q, result)
        core = result['explanation']['cases'][0]['constraints']
        self.assertEqual(len(core), 2)
        source_ids = {i for c in core for i in c['source_ids']}
        self.assertEqual({c['span']['line'] for c in result['constraints'] if c['id'] in source_ids}, {4, 5})

    def test_shared_arithmetic_definitions_and_disabled_selectors(self):
        model = '#word-width 4\nMODULE main\nVAR x : uint4;\nINIT x + 1 = 2;\nINIT x + 1 = 3;\nINIT x < 8;\n'
        q = dict(operation='explain-init', explanation={'minimize': True})
        result = self.job(model, q)
        self.assert_core(model, q, result)
        self.assertEqual(len(result['explanation']['cases'][0]['constraints']), 2)
        empty = dict(operation='explain-init', explanation={'active_ids': []})
        self.assertEqual(self.job(model, empty)['outcome'], 'satisfiable')

    def test_instantiated_enum_domains_and_source_parents(self):
        model = 'MODULE child(p:boolean)\nVAR mode : {A, B};\nINIT mode = A;\nINIT mode = B;\nMODULE main\nVAR item : child(TRUE);\n'
        query = dict(operation='explain-init', explanation={'minimize': True})
        options = ('--root', 'main')
        result = self.job(model, query, options=options)
        self.assert_core(model, query, result, options=options)
        refs = {i for c in result['explanation']['cases'][0]['constraints'] for i in c['source_ids']}
        self.assertTrue(all('@item' in i for i in refs))
        self.assertTrue(all(c['parents'] for c in result['constraints'] if c['id'] in refs))

    def test_shared_conditional_and_array_selection_definitions(self):
        for expression in ['flag ? x + 1 : x + 2', 'data[index]']:
            model = '#word-width 4\nMODULE main\nVAR flag : boolean; x : uint4; data : uint4[2]; index : uint4;\nINVAR index < 2;\n'
            model += f'INIT ({expression}) = 0;\nINIT ({expression}) = 1;\n'
            query = dict(operation='explain-init', explanation={'minimize': True})
            with self.subTest(expression=expression):
                self.assert_core(model, query, self.job(model, query))

    def test_invariant_and_query_assumption_in_core(self):
        model = 'MODULE main\nVAR x : boolean;\nINVAR !x;\n'
        q = dict(operation='explain-init', assumptions=['x'], explanation={'minimize': True})
        result = self.job(model, q)
        self.assert_core(model, q, result)
        self.assertEqual({c['kind'] for c in result['explanation']['cases'][0]['constraints']}, {'invar', 'assumption'})

    def test_pinned_prefix_and_conflicting_continuation(self):
        parent = self.job(TOGGLE, dict(operation='reach', target='x', limits={'depth': 1}))['trace']
        q = dict(operation='explain-step', trace=parent, prefix_length=2, assumptions=['!x'], explanation={'minimize': True})
        result = self.job(TOGGLE, q)
        self.assertEqual((result['scope'], result['explanation']['bound']), ('single_step_continuation', 2))
        self.assert_core(TOGGLE, q, result)
        self.assertIn('assumption', {c['kind'] for c in result['explanation']['cases'][0]['constraints']})
        # Drop all INIT/TRANS constraints: a fixed source value still conflicts.
        pin_ids = ['pin:x:t1', 'assumption:0:t1']
        q['explanation'] = {'active_ids': pin_ids, 'minimize': True}
        self.assert_core(TOGGLE, q, self.job(TOGGLE, q))
        q['assumptions'] = ['x']; q['explanation'] = {}
        self.assertEqual(self.job(TOGGLE, q)['outcome'], 'satisfiable')

    def test_frame_constraints_are_selectable_and_attributed(self):
        model = 'MODULE main\n#inertial\nVAR x : boolean;\nINIT !x;\nTRANS FALSE ?: x := TRUE;\n'
        q = dict(operation='explain-reach', target='x', limits={'depth': 1}, explanation={'minimize': True, 'exact_depth': True})
        result = self.job(model, q)
        self.assert_core(model, q, result)
        self.assertTrue(any(c['id'].startswith('frame:') for c in result['explanation']['cases'][0]['constraints']))
        self.assertTrue(any(c['explanation'].startswith('Preserve') for c in result['constraints']))

    def test_bounded_reach_checks_every_depth_and_handles_dead_ends(self):
        q = dict(operation='explain-reach', target='FALSE', limits={'depth': 2}, explanation={'minimize': True})
        result = self.job(TOGGLE, q)
        self.assertEqual(result['checked_depths'], [0, 1, 2])
        self.assertEqual(result['scope'], 'through_depth')
        self.assert_core(TOGGLE, q, result)
        dead = 'MODULE main\n#inertial\nVAR x : boolean;\nINIT x;\nINVAR x;\nTRANS x := !x;\n'
        q = dict(operation='explain-reach', target='x', limits={'depth': 2})
        self.assertEqual(self.job(dead, q)['outcome'], 'satisfiable')

    def test_shrinking_budget_retains_a_verified_nonminimal_core(self):
        model = 'MODULE main\nVAR x : boolean;\nINIT x;\nINIT !x;\n'
        for budget in ({'checks': 0}, {'wall_ms': 0}):
            q = dict(operation='explain-init', explanation=dict(minimize=True, **budget))
            result = self.job(model, q)
            self.assert_core(model, q, result, delete=False)
            self.assertFalse(result['explanation']['cases'][0]['subset_minimal'])

    def test_unknown_never_reports_an_unsat_core(self):
        for budget in ('wall_ms', 'conflicts', 'propagations'):
            result = self.job(TOGGLE, dict(operation='explain-init', assumptions=['x'], limits={budget: 0}), expected=3)
            self.assertEqual(result['status'], 'unknown')
            self.assertIsNone(result['explanation'])

    def test_invalid_query_and_corrupt_parent_are_rejected(self):
        for query in [dict(operation='explain-init', limits={'depth': 1}), dict(operation='explain-step'),
                      dict(operation='explain-reach', target='x'), dict(operation='explain-init', assumptions=['next(x)']),
                      dict(operation='explain-init', explanation={'active_ids': ['missing']})]:
            self.assertEqual(self.job(TOGGLE, query, expected=2)['status'], 'error')
        parent = self.job(TOGGLE, dict(operation='reach', target='x', limits={'depth': 1}))['trace']
        incomplete = deepcopy(parent); incomplete['steps'][0]['values']['x'] = None
        result = self.job(TOGGLE, dict(operation='explain-step', trace=incomplete), expected=3)
        self.assertEqual(result['stop_reason'], 'solver_unknown')
        self.assertIsNone(result['explanation'])
        parent['steps'][0]['values']['x'] = True
        result = self.job(TOGGLE, dict(operation='explain-step', trace=parent), expected=2)
        self.assertIsNone(result['explanation'])


if __name__ == '__main__':
    unittest.main()
