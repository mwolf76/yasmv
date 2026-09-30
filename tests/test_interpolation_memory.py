#!/usr/bin/env python3
"""Capture/replay correctness, corruption rejection, and profiling isolation."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('memory_runner', ROOT/'tools/benchmark-interpolation-memory.py')
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)

class MemoryBenchmark(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='yasmv-imc-test-')
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)

    def fixture(self):
        artifact = self.path / 'artifact'; artifact.mkdir()
        (artifact/'input.cnf').write_text('yasmv-partitioned-cnf 1\na 1 1 0\nb 2 -1 0\n')
        (artifact/'proof.events').write_text('yasmv-proof-events 1\no a 1 1 0\no b 2 -1 0\ne 1 1 0\nr 1 1 0\nd 3 0 0 1 2 0\nu 3\n')
        (artifact/'interface.json').write_text(json.dumps(dict(format='yasmv-interpolation-capture',version=1,
                         interface=[dict(variable=1,atom=1,symbol='x',bit=0,frozen=False,frame=0)])))
        (artifact/'complete').write_text('verified-unsat\n')
        return artifact

    def replay(self, artifact, mode='events', ok=True, diagnostics=None):
        env = {k:v for k,v in os.environ.items() if not k.startswith('YASMV_IMC_')}
        if diagnostics: env['YASMV_IMC_DIAGNOSTICS'] = str(diagnostics)
        p = subprocess.run([str(ROOT/'interpolation_replay'),str(artifact),mode],env=env,
                           text=True,capture_output=True,timeout=30)
        if not ok:
            self.assertNotEqual(p.returncode,0,p.stdout)
            self.assertFalse(p.stdout.strip(),p.stdout)
            return None
        self.assertEqual(p.returncode,0,p.stderr)
        result=json.loads(p.stdout)
        self.assertTrue(result['verified'])
        self.assertEqual(set(result['obligations'].values()),{'unsatisfiable'})
        return result

    def assert_verification_lifetime(self, samples, destroyed):
        phases=[x['phase'] for x in samples]
        ordered=['interpolant_complete',destroyed,'craig_verification_begin',
                 'craig_verification_end','query_verified','query_temporaries_destroyed']
        positions=[phases.index(phase) for phase in ordered]
        self.assertEqual(positions,sorted(positions))
        before=samples[positions[0]]
        self.assertGreater(before['proof_nodes'],0)
        for sample in samples[positions[1]:positions[3]+1]:
            self.assertFalse(any(key.startswith('proof_') for key in sample),sample)
        for position in positions[1:4]:
            sample=samples[position]
            self.assertEqual(sample['circuit_allocated_nodes'],before['circuit_allocated_nodes'])
            self.assertEqual(sample['circuit_reachable_nodes'],before['circuit_reachable_nodes'])

    def test_replay_and_counters_and_destruction_sample(self):
        artifact=self.fixture(); diagnostics=self.path/'telemetry'
        r=self.replay(artifact,diagnostics=diagnostics)
        self.assertEqual(r['proof_nodes'],3)
        self.assertEqual(r['proof_literals'],2)
        self.assertEqual(r['proof_original_literals'],2)
        self.assertEqual(r['proof_derived_literals'],0)
        self.assertEqual(r['proof_original_clauses'],2)
        self.assertEqual(r['proof_derived_clauses'],1)
        self.assertEqual(r['proof_expanded_literals'],2)
        self.assertEqual(r['proof_active_ids'],3)
        self.assertEqual(r['proof_archived_ids'],3)
        samples=[json.loads(line) for line in (diagnostics/'telemetry.jsonl').read_text().splitlines()]
        self.assert_verification_lifetime(samples,'replay_proof_destroyed')
        ancestry=next(x for x in samples if x['phase']=='proof_ancestry')
        self.assertEqual(ancestry['needed_proof_nodes'],3)
        self.assertEqual(ancestry['original_nodes'],2)
        self.assertTrue(all(x['rss_bytes']>0 for x in samples))
        self.assertLessEqual(r['circuit_reachable_nodes'],r['circuit_allocated_nodes'])
        solve_diagnostics=self.path/'solve-telemetry'
        self.replay(artifact,'solve',diagnostics=solve_diagnostics)
        self.assert_verification_lifetime(
            [json.loads(line) for line in (solve_diagnostics/'telemetry.jsonl').read_text().splitlines()],
            'replay_proof_destroyed')

    def test_reject_corrupt_proof_and_partial_capture(self):
        artifact=self.fixture()
        original=(artifact/'proof.events').read_text()
        for bad in (original.replace('1 2 0\nu','1 99 0\nu'),
                    original.replace('o a 1 1 0','o b 1 1 0'),
                    original.replace('u 3\n',''),original+'u 3\n',
                    original.replace('r 1 1 0\n',''),
                    original.replace('d 3 0','d 3 1'),
                    original.replace('u 3','u 1'),original+'garbage\n'):
            (artifact/'proof.events').write_text(bad)
            self.replay(artifact,ok=False)
        (artifact/'proof.events').write_text(original)
        (artifact/'complete').unlink()
        self.replay(artifact,ok=False)

    def test_reject_foreign_missing_and_aliased_interface(self):
        artifact=self.fixture()
        original=json.loads((artifact/'interface.json').read_text())
        for entries in ([],[dict(variable=2,atom=1)],
                        [dict(variable=1,atom=1),dict(variable=1,atom=2)]):
            m=copy.deepcopy(original); m['interface']=entries
            (artifact/'interface.json').write_text(json.dumps(m))
            self.replay(artifact,ok=False)

    def test_solve_rejects_satisfiable_formula_despite_marker(self):
        artifact=self.fixture()
        (artifact/'input.cnf').write_text('yasmv-partitioned-cnf 1\na 1 1 0\nb 2 1 0\n')
        self.replay(artifact,'solve',ok=False)

    def test_sealed_capture_detects_changes(self):
        artifact=self.fixture()
        hashes=RUNNER.seal(artifact)
        self.assertEqual(set(hashes),set(RUNNER.ARTIFACT_FILES))
        self.assertEqual(hashes,RUNNER.seal(artifact))
        with (artifact/'proof.events').open('a') as stream: stream.write('u 3\n')
        with self.assertRaisesRegex(ValueError,'hash mismatch'): RUNNER.seal(artifact)

    def test_summary_preserves_completed_queries_before_truncated_record(self):
        diagnostics=self.path/'diagnostics'; diagnostics.mkdir()
        (diagnostics/'telemetry.jsonl').write_text(
            '{"phase":"proof_progress","query_index":0,"rss_bytes":100}\n'
            '{"phase":"query_verified","query_index":0,"rss_bytes":80}\n'
            '{"phase":"proof_progress","query_index":1,"rss_bytes":200}\n'
            '{"phase":')
        summary=RUNNER.telemetry_summary(self.path)
        self.assertEqual(summary['samples'],3)
        self.assertEqual(summary['truncated_records'],1)
        self.assertEqual(summary['maxima']['rss_bytes'],200)
        self.assertTrue(summary['queries']['0']['verified'])
        self.assertNotIn('verified',summary['queries']['1'])

    def capture(self, name, images=None, target='GOAL'):
        model=self.path/'model.smv'
        model.write_text('MODULE main\n#inertial VAR x : boolean;\n#inertial VAR y : boolean;\n'
                         'INIT !x && !y;\nTRANS x := !x;\nTRANS y := !y;\nDEFINE GOAL := x != y;\n')
        request=self.path/(name+'.json')
        request.write_text(json.dumps(dict(version=1,model=str(model),query=dict(operation='reach',strategy='interpolation',target=target))))
        diagnostics=self.path/name
        env={k:v for k,v in os.environ.items() if not k.startswith('YASMV_IMC_')}
        env.update(YASMV_HOME=str(ROOT),YASMV_IMC_DIAGNOSTICS=str(diagnostics),YASMV_IMC_CAPTURE='all')
        if images is not None: env['YASMV_IMC_IMAGES']=str(images)
        p=subprocess.run([str(ROOT/'yasmv'),'--quiet','--query-file',str(request)],env=env,
                         text=True,capture_output=True,timeout=60)
        self.assertIn(p.returncode,(0,3),p.stderr+p.stdout)
        return diagnostics,json.loads(p.stdout)

    def test_native_capture_replays_and_image_limit_has_no_certificate(self):
        diagnostics,result=self.capture('full')
        self.assertEqual(result['outcome'],'unreachable')
        self.assertTrue(result['proof']['verified'])
        artifacts=[p for p in diagnostics.glob('query-*') if (p/'complete').read_text()=='verified-unsat\n']
        self.assertGreater(len(artifacts),1)
        samples=[json.loads(line) for line in (diagnostics/'telemetry.jsonl').read_text().splitlines()]
        for index,sample in enumerate(samples):
            if sample['phase']=='query_begin':
                expected='initial_engines_destroyed' if sample['query_index']==0 else 'image_engines_destroyed'
                self.assertEqual(samples[index-1]['phase'],expected)
        for artifact in artifacts:
            self.replay(artifact)
            query=int(artifact.name.removeprefix('query-'))
            self.assert_verification_lifetime(
                [x for x in samples if x.get('query_index')==query], 'proof_engine_destroyed')
        phases=[x['phase'] for x in samples]
        self.assertEqual(phases.count('image_engines_destroyed'),phases.count('image_cnf_destroyed'))
        _,limited=self.capture('prefix',1)
        self.assertEqual(limited['status'],'unknown')
        self.assertTrue(limited['statistics']['interpolation']['image_limit_reached'])
        self.assertIsNone(limited['proof'])
        self.assertIsNone(limited['trace'])

    def test_reachable_control_is_not_a_verified_unsat_capture(self):
        diagnostics,result=self.capture('reachable',target='x')
        self.assertEqual(result['outcome'],'reachable')
        rejected=[p for p in diagnostics.glob('query-*') if (p/'complete').read_text()=='not-verified\n']
        self.assertTrue(rejected)
        for artifact in rejected: self.replay(artifact,ok=False)
        request=self.path/'replay.json'
        request.write_text(json.dumps(dict(version=1,model=str(self.path/'model.smv'),
                            query=dict(operation='validate-trace',trace=result['trace']))))
        env={k:v for k,v in os.environ.items() if not k.startswith('YASMV_IMC_')}
        p=subprocess.run([str(ROOT/'yasmv'),'--quiet','--query-file',str(request)],
                         env=dict(env,YASMV_HOME=str(ROOT)),capture_output=True,text=True,timeout=30)
        self.assertEqual(p.returncode,0,p.stderr)
        self.assertEqual(json.loads(p.stdout)['outcome'],'valid')

if __name__=='__main__': unittest.main()
