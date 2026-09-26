#!/usr/bin/env python3
"""M3 export, implementation replay, provenance, and malformed artifact gates."""
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.workbench.engine import Engine, atomic, read
from tools.scenario.format import build, digest, metadata, typed, validate
from tools.scenario.replay import replay


class ScenarioTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.engine = Engine(Path(cls.temp.name) / 'store')
        cls.mapping = read(ROOT / 'examples/retry-protocol/scenario.json')
        cls.rev = cls.engine.save_revision(dict(source=(ROOT / 'examples/retry-protocol/faulty.smv').read_text(), scenario=cls.mapping))
        cls.found = cls.job(dict(operation='reach', target='DUPLICATE', limits={'depth': 12}))
        if cls.found.get('outcome') != 'reachable':
            raise RuntimeError(cls.found)
        cls.exported = cls.job(dict(operation='export-scenario', trace_id=cls.found['trace_id']))
        if cls.exported.get('outcome') != 'exported':
            raise RuntimeError(cls.exported)
        cls.scenario = cls.engine.scenario(cls.exported['scenario_id'])

    @classmethod
    def tearDownClass(cls):
        cls.engine.close(); cls.temp.cleanup()

    @classmethod
    def job(cls, query, rev=None):
        identifier = cls.engine.submit(dict(version=1, request_id=str(uuid.uuid4()), revision=(rev or cls.rev)['id'], query=query))
        end = time.monotonic() + 90
        while cls.engine.job(identifier)['running']:
            if time.monotonic() > end: raise TimeoutError(identifier)
            time.sleep(.05)
        return cls.engine.job(identifier)['result']

    def test_export_retains_context_types_and_replay_policy(self):
        value = self.scenario
        self.assertEqual(value['revision'], self.rev['id'])
        self.assertEqual(value['model_identity'], self.found['trace']['identity'])
        self.assertEqual(value['query']['target'], 'DUPLICATE')
        self.assertEqual(value['query']['limits']['depth'], 12)
        self.assertEqual(value['observations']['executions']['type'], {'kind': 'integer', 'signed': False, 'width': 4})
        self.assertEqual([a['action'] for a in value['actions']], ['SEND', 'DELIVER', 'DROP_ACK', 'RETRY', 'DELIVER'])
        self.assertEqual(value['actions'][-1]['expected']['executions'], '2')
        self.assertEqual(value['actions'][0]['arguments']['job_id'], {'type': {'kind': 'string'}, 'value': 'job-1'})
        self.assertEqual(value['policy']['final_action'], 'not_executed')
        self.assertEqual(value['trace_identity']['digest'], digest(self.found['trace']))
        self.assertEqual(validate(value), value)

    def test_faulty_reproduces_and_corrected_diverges_at_exact_step(self):
        faulty = self.job(dict(operation='replay-scenario', scenario_id=self.scenario['id'], implementation='faulty'))
        fixed = self.job(dict(operation='replay-scenario', scenario_id=self.scenario['id'], implementation='deduplicating'))
        self.assertEqual(faulty['outcome'], 'matched', faulty)
        self.assertTrue(faulty['implementation_replay']['duplicate_execution'])
        self.assertEqual(fixed['outcome'], 'diverged', fixed)
        self.assertFalse(fixed['implementation_replay']['duplicate_execution'])
        self.assertEqual(fixed['implementation_replay']['first_divergence'], dict(step=5, action='DELIVER', field='executions', expected='2', actual='1'))
        self.assertEqual(fixed['implementation_replay']['model_trace_validation'], 'recorded_at_export_not_rechecked')

    def test_tampering_is_detected_and_changed_expectations_localize_divergence(self):
        altered = deepcopy(self.scenario)
        altered['actions'][1]['expected']['executions'] = '0'
        with self.assertRaisesRegex(ValueError, 'integrity'): replay(altered)
        # A deliberately edited scenario must acquire a new content ID.
        altered['id'] = digest({k: v for k, v in altered.items() if k != 'id'})
        result = replay(altered)
        self.assertEqual(result['first_divergence'], dict(step=2, action='DELIVER', field='executions', expected='0', actual='1'))
        self.assertEqual(result['actions_executed'], 2)
        self.assertEqual(self.engine.scenario(self.scenario['id']), self.scenario)

    def test_missing_action_observation_or_argument_mapping_is_rejected(self):
        for key in ('mapping', 'observations', 'arguments'):
            value = deepcopy(self.mapping)
            value['actions'][key].pop(next(iter(value['actions'][key])))
            with self.subTest(key=key), self.assertRaises(ValueError): metadata(value)
        value = deepcopy(self.mapping); value['adapter'] = '/bin/sh'
        with self.assertRaises(ValueError): metadata(value)
        value = deepcopy(self.mapping); value['actions']['mapping']['SEND'] = 'SHELL'
        with self.assertRaises(ValueError): metadata(value)

    def test_malformed_portable_scenarios_fail_before_execution(self):
        for field, bad in [('policy', {}), ('model_trace_validation', {}), ('version', 2), ('actions', None)]:
            altered = deepcopy(self.scenario); altered[field] = bad
            altered['id'] = digest({k: v for k, v in altered.items() if k != 'id'})
            with self.subTest(field=field), self.assertRaises(ValueError): replay(altered)
        altered = deepcopy(self.scenario); altered['observations']['phase']['type'] = None
        altered['id'] = digest({k: v for k, v in altered.items() if k != 'id'})
        with self.assertRaisesRegex(ValueError, 'type'): replay(altered)

    def test_export_requires_exact_replay_and_mapped_symbols(self):
        trace = self.found['trace']
        with self.assertRaises(ValueError): build(trace, self.mapping, dict(status='completed', outcome='valid', trace={}))
        bad = deepcopy(trace); bad['steps'][0]['values']['executions'] = '1'
        result = self.job(dict(operation='export-scenario', trace=bad))
        self.assertNotIn('scenario_id', result)
        value = deepcopy(self.mapping); value['actions']['symbol'] = 'missing'
        with self.assertRaises(ValueError): build(trace, value, dict(status='completed', outcome='valid', trace=trace))

    def test_exact_numeric_values_and_width_rejections(self):
        typ = dict(kind='integer', signed=False, width=64)
        self.assertEqual(typed('18446744073709551615', typ), '18446744073709551615')
        for value in ['18446744073709551616', '-1', '01', 1.0, None]:
            with self.assertRaises(ValueError): typed(value, typ)
        self.assertEqual(typed('-9223372036854775808', dict(typ, signed=True)), '-9223372036854775808')

    def test_standalone_export_and_replay_without_server(self):
        directory = Path(self.temp.name)
        trace = directory / 'trace.json'; atomic(trace, self.found['trace'])
        output = directory / 'scenario.json'
        process = subprocess.run([sys.executable, '-m', 'tools.scenario', 'export', str(trace), '--metadata', str(ROOT / 'examples/retry-protocol/scenario.json'),
                                  '--model', str(ROOT / 'examples/retry-protocol/faulty.smv'), '--output', str(output)], cwd=ROOT, capture_output=True, text=True, timeout=90)
        self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
        for implementation, code in [('faulty', 0), ('deduplicating', 3)]:
            p = subprocess.run([sys.executable, '-m', 'tools.scenario', 'replay', str(output), '--implementation', implementation],
                               cwd=ROOT, capture_output=True, text=True, timeout=10)
            self.assertEqual(p.returncode, code, p.stdout + p.stderr)
            self.assertEqual(json.loads(p.stdout)['duplicate_execution'], implementation == 'faulty')

    def test_explanation_jobs_share_trace_identity_and_persist(self):
        result = self.job(dict(operation='explain-step', trace_id=self.found['trace_id'], prefix_length=1,
                               assumptions=['action = ACK'], explanation={'minimize': True}))
        self.assertEqual(result['outcome'], 'unsatisfiable', result)
        self.assertEqual(result['identity'], self.found['identity'])
        self.assertTrue(result['explanation']['cases'][0]['subset_minimal'])
        self.assertEqual(self.engine.job(result['request_id'])['request']['query']['trace_id'], self.found['trace_id'])
        other = self.engine.save_revision(dict(source=self.rev['source'] + '\n', scenario=self.mapping))
        with self.assertRaises(ValueError):
            self.job(dict(operation='replay-scenario', scenario_id=self.scenario['id'], implementation='faulty'), other)


if __name__ == '__main__':
    unittest.main()
