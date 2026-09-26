#!/usr/bin/env python3
"""Universal eventuality, independent fixed-point oracle, artifacts and clients."""
from copy import deepcopy
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import threading
import time
import unittest

# Sanitizers need more time; zero-budget and state-limit checks remain unchanged.
WALL_MS = int(os.environ.get('YASMV_PROGRESS_TEST_WALL_MS', '15000'))
QUERY_TIMEOUT = WALL_MS / 1000 + 10

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.workbench.sessions import Session
from tools.workbench.client import Client


def graph_model(edges, initial=(0,)):
    n = len(edges)
    width = max(1, n.bit_length())
    relation = '\n'.join('TRANS x = %d ?: x := %s;' % (state, '{' + ','.join(map(str,dests)) + '}' if len(dests)>1 else str(dests[0] if dests else n)) for state,dests in enumerate(edges))
    init = ' || '.join(f'x = {s}' for s in initial) or 'FALSE'
    return f'#word-width {width}\nMODULE main\n#inertial\nVAR x: uint{width};\nINIT {init};\nINVAR x <= {n-1};\n{relation}\n'


def inevitable(edges, initial, goals):
    # Least fixed point, independent of the checker's forward cycle/rank method.
    done = set(goals)
    while True:
        more = {s for s, dests in enumerate(edges) if dests and set(dests) <= done}
        if more <= done:
            return set(initial) <= done
        done |= more


class ProgressTests(unittest.TestCase):
    def session(self, source, inputs=None, root=""):
        s = Session(str(ROOT / 'yasmv'), str(ROOT), dict(source=source, root=root, inputs=inputs or {}), threading.Event(), time.monotonic() + 90)
        self.addCleanup(s.close)
        return s

    def query(self, s, target='x = 2', **kwargs):
        q = dict(request_id='progress', operation='check-progress', target=target, limits=dict(states=1000, wall_ms=WALL_MS))
        q.update(kwargs)
        return s.query(q, threading.Event(), time.monotonic() + QUERY_TIMEOUT)

    def replay(self, s, artifact, **kwargs):
        q = dict(request_id='replay', operation='validate-progress', progress=artifact, limits=dict(states=1000, wall_ms=WALL_MS))
        q.update(kwargs)
        return s.query(q, threading.Event(), time.monotonic() + QUERY_TIMEOUT)

    def decision(self, s, target, expected):
        r = self.query(s, target)
        self.assertEqual((r['status'], r['outcome']), ('completed', expected), r)
        self.assertEqual(r['scope'], 'unbounded')
        self.assertEqual(self.replay(s, r['progress'])['outcome'], 'valid')
        return r

    def test_all_two_state_relations_against_oracle(self):
        for mask in range(16):
            edges = [[t for t in range(2) if mask & (1 << (2*s+t))] for s in range(2)]
            for initial in ((0,), (0, 1)):
                s = self.session(graph_model(edges, initial))
                for goals in ((), (0,), (1,), (0, 1)):
                    with self.subTest(edges=edges, initial=initial, goals=goals):
                        target = ' || '.join(f'x = {v}' for v in goals) or 'FALSE'
                        self.decision(s, target, 'proven' if inevitable(edges, initial, goals) else 'violated')
                s.close()

    def test_larger_nondeterministic_graphs(self):
        rng = random.Random(617)
        cases = [([ [1,2], [3], [3], [] ], (0,), (3,)),
                 ([[1], [2,3], [1], []], (0,), (3,)),
                 ([[1], [], [2], []], (0,), (1,))]
        for _ in range(15):
            edges = [[t for t in range(4) if rng.randrange(4) == 0] for _ in range(4)]
            cases.append((edges, (0, 2), (3,)))
        for edges, initial, goals in cases:
            with self.subTest(edges=edges):
                s = self.session(graph_model(edges, initial))
                self.decision(s, 'x = 3' if goals == (3,) else 'x = 1', 'proven' if inevitable(edges, initial, goals) else 'violated')
                s.close()

    def test_initial_success_deadends_assumptions_and_vacuity(self):
        s = self.session(graph_model([[1], [2], [2]]))
        self.decision(s, 'x = 0', 'proven')  # need only visit once
        r = self.query(s, assumptions=['x < 2'])
        self.assertEqual(r['progress']['kind'], 'deadlock', r)
        self.assertEqual(self.replay(s, r['progress'])['outcome'], 'valid')
        r = self.query(s, assumptions=['FALSE'])
        self.assertTrue(r['proof']['vacuous'], r)
        empty = self.session(graph_model([[0]], ()))
        self.assertTrue(self.decision(empty, 'FALSE', 'proven')['progress']['vacuous'])

    def test_state_identity_types_and_empty_state(self):
        # Same visible x with different frozen f must remain distinct.
        source = 'MODULE main\n#frozen\nVAR f:boolean;\n#inertial\nVAR x:boolean;\nINIT !x;\nTRANS x := f;\n'
        s = self.session(source)
        self.decision(s, 'x', 'violated')
        source = '#word-width 64\nMODULE main\n#input\nVAR enable:boolean;\n#inertial #hidden\nVAR h:boolean;\n#inertial\nVAR e:{A,B,C};\n#inertial\nVAR a:boolean[2];\n#inertial\nVAR n:uint64;\nINIT !h && e = A && a = [FALSE, TRUE] && n = 18446744073709551615;\nTRANS h := enable;\nTRANS e := B;\nTRANS a := [TRUE, FALSE];\nTRANS n := n;\n'
        s = self.session(source, {'enable':'TRUE'})
        r = self.decision(s, 'h', 'proven')
        self.assertEqual(r['progress']['nodes'][0]['values']['n'], '18446744073709551615')
        s = self.session('#word-width 64\nMODULE main\nVAR a:{A,B,C}[2];\n#frozen\nVAR n:int64;\nINIT a = [A,B] && n = -9223372036854775808;\n')
        r = self.decision(s, 'FALSE', 'violated')
        self.assertEqual(r['trace']['steps'][0]['values']['n'], '-9223372036854775808')
        self.assertEqual(r['trace']['steps'][0]['values']['a'], ['A','B'])
        s = self.session('MODULE main\nINIT TRUE;\n')
        self.decision(s, 'FALSE', 'violated')
        self.decision(s, 'TRUE', 'proven')

    def test_limits_and_invalid_requests(self):
        s = self.session(graph_model([[1], [2], []]))
        self.assertEqual(self.query(s, limits=dict(states=2, wall_ms=WALL_MS))['outcome'], 'proven')
        for limit, value in (('states',1), ('wall_ms',0), ('conflicts',0), ('propagations',0)):
            r = self.query(s, limits=dict(dict(states=100, wall_ms=WALL_MS), **{limit:value}))
            self.assertEqual(r['status'], 'unknown', r)
            self.assertIsNone(r.get('progress'))
            self.assertIsNone(r['outcome'])
        for options in (dict(target='next(x) = 2'), dict(target='x'), dict(target='x = {0,1}'), dict(assumptions=['x = {0,1}']), dict(fairness=['TRUE']),
                        dict(limits=dict(depth=2, states=100, wall_ms=WALL_MS)), dict(limits=dict(states=0, wall_ms=WALL_MS))):
            r = self.query(s, **options)
            self.assertEqual(r['status'], 'error', r)

    def test_nonlocal_models_rejected(self):
        for constraint in ('INVAR @0{x};', 'TRANS x := next(next(x));', 'DEFINE late := next(x);\nTRANS x := next(late);', 'DEFINE late := next(x);\nINIT late;'):
            with self.subTest(constraint=constraint):
                s = self.session('MODULE main\n#inertial\nVAR x:boolean;\n'+constraint+'\n')
                r = self.query(s, 'x')
                self.assertEqual(r['status'], 'error', r)

    def test_proof_tampering_and_budgeted_replay(self):
        s = self.session(graph_model([[1], [2], []]))
        a = self.decision(s, 'x = 2', 'proven')['progress']
        for mutate in (lambda x: x['nodes'].pop(),
                       lambda x: x['nodes'][0].update(rank=0),
                       lambda x: x.update(vacuous=True),
                       lambda x: x['nodes'][0].update(edges=[]),
                       lambda x: x['nodes'][-1].update(goal_exit=False),
                       lambda x: x['nodes'][0]['values'].update(x='3'),
                       lambda x: x.update(unexpected=True)):
            b = deepcopy(a); mutate(b)
            r = self.replay(s,b)
            self.assertNotEqual(r.get('outcome'), 'valid', r)
        for limit in ('wall_ms', 'conflicts', 'propagations'):
            r = self.replay(s, a, limits=dict(dict(states=100, wall_ms=WALL_MS), **{limit:0}))
            self.assertEqual(r['status'], 'unknown', r)
        r = self.replay(s, a, limits=dict(states=1, wall_ms=WALL_MS))
        self.assertEqual(r['status'], 'unknown', r)
        self.assertEqual(r['stop_reason'], 'state_limit', r)
        self.assertIsNone(r.get('progress'))
        self.assertEqual(self.replay(s, a, assumptions=['x = 0'])['status'], 'error')

    def test_counterexample_tampering(self):
        s = self.session(graph_model([[1], [0,2], []]))
        a = self.decision(s, 'x = 2', 'violated')['progress']
        r = self.replay(s, a, limits=dict(states=1, wall_ms=WALL_MS))
        self.assertEqual(r['status'], 'unknown', r)
        self.assertEqual(r['stop_reason'], 'state_limit', r)
        self.assertIsNone(r.get('progress'))
        self.assertEqual(a['kind'], 'loop')
        for mutate in (lambda x: x.update(loop_start=100),
                       lambda x: x.update(loop_start=len(x['trace']['steps'])-1),
                       lambda x: x['query'].update(target='x = 0'),
                       lambda x: x['trace']['steps'][0]['values'].pop('x'),
                       lambda x: x['identity'].update(root='wrong')):
            b=deepcopy(a); mutate(b)
            self.assertNotEqual(self.replay(s,b).get('outcome'), 'valid')
        b=deepcopy(a); b['kind']='deadlock'; b.pop('loop_start')
        self.assertEqual(self.replay(s,b)['outcome'], 'invalid')
        # A goal-reaching successor invalidates a claimed dead end too.
        s=self.session(graph_model([[1], []]))
        a=self.decision(s,'FALSE','violated')['progress']
        a['trace']['steps']=a['trace']['steps'][:1]
        self.assertEqual(self.replay(s,a)['outcome'], 'invalid')

    def test_retry_and_examples(self):
        for model in ('faulty','deduplicating'):
            s=self.session((ROOT/f'examples/retry-protocol/{model}.smv').read_text())
            self.decision(s,'SUCCEEDED || EXHAUSTED','proven')
            self.decision(s,'SUCCEEDED','violated')
        for model,outcome,kind in (('complete','proven','proof'),('stalled','violated','deadlock'),('retry-forever','violated','loop')):
            s=self.session((ROOT/f'examples/progress/{model}.smv').read_text())
            self.assertEqual(self.decision(s,'FINISHED',outcome)['progress']['kind'],kind)

    def test_modules_and_temporal_parameters(self):
        source = 'MODULE child(p:boolean)\nVAR x:boolean;\nINIT x=p;\nMODULE main\nVAR a:child(TRUE); b:child(FALSE);\n'
        s=self.session(source, root='main')
        self.decision(s,'a.x && !b.x','proven')
        self.decision(s,'FALSE','violated')
        temporal=source.replace('child(TRUE)', 'child(next(a.x))', 1)
        s=self.session(temporal, root='main')
        self.assertEqual(self.query(s,'a.x')['status'],'error')

    def test_schemas_and_capabilities(self):
        try:
            import jsonschema
        except ImportError:
            self.skipTest('optional jsonschema is not installed')
        directory=ROOT/'docs/formats'
        store={p.as_uri():json.loads(p.read_text()) for p in directory.glob('*.json')}
        def validate(name,value):
            schema=json.loads((directory/name).read_text())
            schema['$id']=(directory/name).as_uri()
            jsonschema.Draft202012Validator(schema,resolver=jsonschema.RefResolver(base_uri=schema["$id"],referrer=schema,store=store)).validate(value)
        s=self.session(graph_model([[1], [0,2], []]))
        for target in ('x = 2','TRUE'):
            r=self.query(s,target)
            self.assertEqual(r['status'],'completed',r)
            kind='proof' if r['progress']['kind']=='proof' else 'counterexample'
            validate(f'progress-{kind}-v1.schema.json',r['progress'])
            validate('analysis-v1.schema.json',r)
            q=dict(operation='check-progress',target=target,limits=dict(states=1000,wall_ms=WALL_MS))
            validate('query-v1.schema.json',dict(version=1,model='model.smv',query=q))
            validate('workbench-v1.schema.json',dict(version=1,request_id='schema',revision='a'*64,query=q))
        from tools.workbench.client import OPERATIONS
        schema=json.loads((directory/'cli-v1.schema.json').read_text())
        self.assertEqual(set(schema['properties']['operation']['enum']),set(OPERATIONS))

    def test_cnf_configurations(self):
        with tempfile.TemporaryDirectory() as d:
            model=Path(d)/'model.smv'; request=Path(d)/'request.json'
            model.write_text(graph_model([[1],[2],[2]]))
            for mask in range(8):
                options=[]
                for bit,name in enumerate(('tautology-removal','duplicate-removal','subsumption')):
                    options += ['--cnf-'+name, 'yes' if mask & (1<<bit) else 'no']
                for target,expected in (('x = 2','proven'),('FALSE','violated')):
                    request.write_text(json.dumps(dict(version=1,model=str(model),query=dict(operation='check-progress',target=target,limits=dict(states=100,wall_ms=WALL_MS)))))
                    run=subprocess.run([str(ROOT/'yasmv'),'--quiet','--query-file',str(request),*options],env=dict(os.environ,YASMV_HOME=str(ROOT)),capture_output=True,text=True,timeout=QUERY_TIMEOUT)
                    self.assertEqual(run.returncode,0,run.stdout+run.stderr)
                    result=json.loads(run.stdout)
                    self.assertEqual(result['outcome'],expected,result)

    def test_progress_prefix_requires_explicit_scenario_conversion(self):
        with tempfile.TemporaryDirectory() as d:
            client=Client(Path(d)/'store',str(ROOT/'yasmv'),str(ROOT))
            self.addCleanup(client.close)
            example=ROOT/'examples/retry-protocol'
            loaded=client.dispatch('model.load',dict(file=str(example/'faulty.smv'),metadata=str(example/'scenario.json')))
            revision=loaded['revision']
            found=client.query(dict(revision=revision,query=dict(operation='check-progress',target='SUCCEEDED',limits=dict(states=1000,wall_ms=WALL_MS))))
            self.assertEqual(found['outcome'],'violated',found)
            blocked=client.dispatch('scenario.export',dict(revision=revision,trace_id=found['trace_id']))
            self.assertEqual(blocked['status'],'error',blocked)
            prefix=Path(d)/'prefix.json'
            client.dispatch('trace.export',dict(trace_id=found['trace_id'],file=str(prefix)))
            imported=client.dispatch('trace.import',dict(revision=revision,file=str(prefix)))
            self.assertNotEqual(imported['trace_id'],found['trace_id'])
            exported=client.dispatch('scenario.export',dict(revision=revision,trace_id=imported['trace_id']))
            self.assertEqual(exported['outcome'],'exported',exported)

    def test_cli_agent_persistence(self):
        with tempfile.TemporaryDirectory() as d:
            store=Path(d)/'store'; artifact=Path(d)/'progress.json'
            commands=f'workspace open "{store}"\nread-model "examples/progress/retry-forever.smv"\ncheck-progress FINISHED\nexport-progress "{artifact}"\nvalidate-progress "{artifact}"\ndump-trace\n'
            p=subprocess.run([str(ROOT/'yasmv'),'--quiet'],input=commands,text=True,capture_output=True,cwd=ROOT,env=dict(os.environ,YASMV_HOME=str(ROOT)),timeout=60)
            self.assertEqual(p.returncode,0,p.stdout+p.stderr)
            self.assertIn('Guaranteed progress violated',p.stdout)
            self.assertIn('Progress artifact validated',p.stdout)
            self.assertEqual(json.loads(artifact.read_text())['kind'],'loop')
            client=Client(store,str(ROOT/'yasmv'),str(ROOT))
            self.addCleanup(client.close)
            jobs=sorted(store.glob('jobs/*/result.json'))
            job=next(p.parent.name for p in jobs if json.loads(p.read_text()).get('outcome')=='violated')
            self.assertEqual(client.dispatch('progress.show',dict(job_id=job))['data']['kind'],'loop')
            revision=client.engine.revisions()[0]['id']
            r=client.query(dict(revision=revision,query=dict(operation='validate-progress',progress=json.loads(artifact.read_text()),limits=dict(states=1000,wall_ms=WALL_MS))))
            self.assertEqual(r['outcome'],'valid',r)
            self.assertTrue(r['evidence']['progress'])

if __name__=='__main__': unittest.main()
