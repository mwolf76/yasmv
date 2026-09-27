#!/usr/bin/env python3
"""M3 call semantics, verifier hooks, source evidence, and controlled C workflow."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import unittest

import test_llvm2smv_scalar as scalar
from test_llvm2smv_scalar import ROOT, BINARY, CHECKER, CLANG, prop, symbol
sys.path.insert(0, str(ROOT / 'tools'))
from llvm2smv_artifact import check_artifact, ArtifactError


class CWorkflowTests(unittest.TestCase):
    setUp = scalar.ScalarTests.setUp
    candidate = scalar.ScalarTests.candidate
    bundle = scalar.ScalarTests.bundle
    query = scalar.ScalarTests.query
    reach = scalar.ScalarTests.reach

    def driver(self, source, *options, status=None, code=0):
        self.serial += 1
        if isinstance(source, str):
            path = self.path / f'program-{self.serial}.c'
            path.write_text(source)
            source = path
        destination = self.path / f'c-bundle-{self.serial}'
        command = [sys.executable, str(ROOT / 'tools/verify-c.py'), str(source), '-o', str(destination),
                   '--translator', BINARY, '--checker', CHECKER, '--clang', CLANG, '--depth', '45', '--timeout', '60', *options]
        result = subprocess.run(command, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        if status: self.assertEqual(report['status'], status, report)
        return report, destination, command

    def test_safe_unsafe_source_evidence_and_native_execution(self):
        for name, expected, code in [('unsafe', 'violation', 1), ('safe', 'holds_through_depth', 0)]:
            source = ROOT / f'tests/llvm2smv/safety/{name}.c'
            report, bundle, _ = self.driver(source, status=expected, code=code)
            if name == 'unsafe':
                self.assertEqual(report['replay']['outcome'], 'valid')
                self.assertEqual(report['failure_site']['inline_chain'][0]['line'], 9)
                self.assertTrue(report['failure_site']['inline_chain'][0]['file'].endswith('unsafe.c'))
                picks = [f['nondeterministic_value'] for f in report['source_trace']['frames'] if 'nondeterministic_value' in f]
                self.assertEqual(picks, ['2'])
                self.assertFalse(report['translation_certified'])
                trace = copy.deepcopy(report['trace'])
                trace['steps'][-1]['values']['v_7063'] = trace['steps'][0]['values']['v_7063']
                self.assertEqual(self.query(bundle, 'validate-trace', trace=trace)['outcome'], 'invalid')
            else:
                self.assertEqual(report['unbounded_outcome'], 'unknown')
            # Independent native execution with the witness input for these defined fixtures.
            runtime = self.path / 'runtime.c'
            runtime.write_text('''#include <stdlib.h>
int __VERIFIER_nondet_int(void) { return 2; }
void __VERIFIER_assume(int x) { if (!x) exit(77); }
void __VERIFIER_assert(int x) { if (!x) exit(42); }
''')
            exe = self.path / 'native'
            subprocess.run([CLANG, '-O0', '-I', str(ROOT / 'llvm2smv/runtime'), str(source), str(runtime), '-o', str(exe)], check=True, capture_output=True)
            self.assertEqual(subprocess.run([str(exe)]).returncode, 42 if name == 'unsafe' else 0)

    def test_inline_nested_side_effects_returns_and_calls_in_loops(self):
        model = self.bundle('''@g=global i8 0, align 1
define i8 @add(i8 %a) {
 %g=load i8, ptr @g, align 1
 %n=add i8 %g,1
 store i8 %n, ptr @g, align 1
 %c=icmp eq i8 %a,0
 br i1 %c,label %zero,label %nonzero
zero: ret i8 3
nonzero: %v=add i8 %a,2
 ret i8 %v
}
define i8 @nested(i8 %x) { %a=call i8 @add(i8 %x)
 %b=call i8 @add(i8 %a)
 ret i8 %b }
define i8 @main() { br label %loop
loop: %i=phi i8 [0,%0],[%n,%loop]
 %x=call i8 @nested(i8 %i)
 %n=add i8 %i,1
 %again=icmp ult i8 %n,2
 br i1 %again,label %loop,label %exit
exit: ret i8 %x }
''')
        result=self.reach(model, prop('terminated'), 70)
        self.assertEqual(result['outcome'], 'reachable')
        final=result['trace']['steps'][-1]['values']
        self.assertEqual(final[symbol('return')], '5')
        self.assertEqual(final[symbol('global.g')], '4')
        self.assertEqual(self.query(model,'validate-trace',trace=result['trace'])['outcome'],'valid')

    def test_inlining_preserves_unused_ub_and_noundef(self):
        cases=[
            ('define i8 @f() { %x=sdiv i8 1,0\nret i8 7 }', '%x=call i8 @f()'),
            ('define i8 @f(i8 noundef %x) { ret i8 7 }', '%x=call i8 @f(i8 poison)'),
            ('define i8 @f(i8 %x) { ret i8 7 }', '%x=call i8 @f(i8 noundef poison)'),
            ('define noundef i8 @f() { ret i8 poison }', '%x=call i8 @f()'),
            ('define i8 @f() { ret i8 poison }', '%x=call noundef i8 @f()'),
            ('define i8 @f(i1 %c) { br i1 %c,label %a,label %b\na: ret i8 1\nb: ret i8 2 }', '%x=call i8 @f(i1 poison)'),
        ]
        for definition, call in cases:
            with self.subTest(definition=definition, call=call):
                model=self.bundle(definition+'\ndefine i8 @main() { '+call+'\nret i8 0 }')
                self.assertEqual(self.reach(model,prop('runtime_error'),10)['outcome'],'reachable')
                self.assertEqual(self.reach(model,prop('terminated'),10)['outcome'],'unreachable')

    def test_repeated_nondet_is_fresh_and_stored_values_stable(self):
        model=self.bundle('''declare i1 @__VERIFIER_nondet_bool()
declare void @__VERIFIER_assert(i32)
define i8 @main() {
 %a=call i1 @__VERIFIER_nondet_bool()
 %b=call i1 @__VERIFIER_nondet_bool()
 %same=icmp eq i1 %a,%b
 %cond=zext i1 %same to i32
 call void @__VERIFIER_assert(i32 %cond)
 ret i8 0
}''')
        self.assertEqual(self.reach(model,prop('assertion_failed'),7)['outcome'],'reachable')
        self.assertEqual(self.reach(model,prop('terminated'),7)['outcome'],'reachable')
        model=self.bundle('''declare i1 @__VERIFIER_nondet_bool()
define i8 @main() { br label %loop
loop: %n=call i1 @__VERIFIER_nondet_bool()
 br i1 %n,label %exit,label %loop
exit: ret i8 0 }''')
        result=self.reach(model,prop('terminated'),8)
        self.assertEqual(result['outcome'],'reachable')
        self.assertEqual(self.query(model,'validate-trace',trace=result['trace'])['outcome'],'valid')

    def test_false_assumption_exits_without_a_termination_failure(self):
        report, _, _=self.driver('#include <yasmv.h>\nint main(void) { __VERIFIER_assume(0); __VERIFIER_error(); }',
                                '--check','termination',status='no_admitted_execution')
        self.assertEqual(report['backend']['outcome'],'proven')
        self.assertEqual(report['replay']['outcome'],'valid')
        self.assertFalse(report['admitted_execution'])
        report, _, _=self.driver('int main(void) { for (;;) {} }','--check','termination',status='violation',code=1)
        self.assertEqual(report['replay']['outcome'],'valid')

    def test_hook_signatures_and_full_call_graph_rejections(self):
        cases=[
            'define i8 @f(i8 %x) { %v=call i8 @f(i8 %x)\nret i8 %v }\ndefine i8 @main() { %v=call i8 @f(i8 0)\nret i8 %v }',
            'declare void @unknown()\ndefine void @f() { call void @unknown()\nret void }\ndefine void @main() { br i1 false,label %dead,label %done\ndead: call void @f()\nbr label %done\ndone: ret void }',
            'define i8 @f(i8 %x) mustprogress { ret i8 %x }\ndefine i8 @main() { %v=call i8 @f(i8 0)\nret i8 %v }',
            'declare i32 @__VERIFIER_nondet_bool()\ndefine i32 @main() { %v=call i32 @__VERIFIER_nondet_bool()\nret i32 %v }',
            'declare void @__VERIFIER_assert(i1)\ndefine void @main() { call void @__VERIFIER_assert(i1 false)\nret void }',
            'define void @__VERIFIER_error() { ret void }\ndefine void @main() { call void @__VERIFIER_error()\nret void }',
            'declare void @__llvm2smv_defined_8(i8)\ndefine void @main() { ret void }',
            'declare void @llvm.assume(i1)\ndefine void @main() { call void @llvm.assume(i1 true)\nret void }',
            'define i8 @f(i8 %x) { ret i8 %x }\ndefine i8 @main() { %v=call i8 @f(i8 0) [ "unknown"() ]\nret i8 %v }',
        ]
        for source in cases:
            with self.subTest(source=source): self.candidate(source,ok=False)

    def test_build_provenance_determinism_and_output_preservation(self):
        source=self.path/'input.c'; source.write_text('#include <assert.h>\nint main(void) { assert(1); return 0; }')
        a,bundle,command=self.driver(source,status='holds_through_depth',*['--depth','10'])
        b,other,_=self.driver(source,status='holds_through_depth',*['--depth','10'])
        self.assertEqual(a['artifact_id'],b['artifact_id'])
        provenance=json.loads((bundle/'provenance.json').read_text())
        self.assertIn('preprocessed_sha256',provenance['c_build']['units'][0])
        self.assertIn('assert.h',provenance['c_build']['runtime'])
        manifest=(bundle/'manifest.json').read_bytes()
        rerun=subprocess.run(command,capture_output=True,text=True,timeout=10)
        self.assertEqual(rerun.returncode,2)
        self.assertEqual((bundle/'manifest.json').read_bytes(),manifest)
        artifact=dict(version=1,files={p.name:p.read_text() for p in bundle.iterdir()})
        artifact['files']['source-map.json']+=' '
        with self.assertRaises(ArtifactError): check_artifact(artifact)

    def test_multi_unit_calls_and_inline_source_chain(self):
        helper=self.path/'helper.c'
        helper.write_text('#include <assert.h>\nint helper(int x) { assert(x == 0); return x; }')
        source=self.path/'main.c'
        source.write_text('int helper(int);\nint main(void) { return helper(1); }')
        report,_,_=self.driver(source,str(helper),status='violation',code=1)
        chain=report['failure_site']['inline_chain']
        self.assertEqual([frame['line'] for frame in chain],[2,2])
        self.assertTrue(chain[0]['file'].endswith('helper.c'))
        self.assertTrue(chain[1]['file'].endswith('main.c'))

    def test_limits_are_not_proofs(self):
        report,_,_=self.driver('int main(void) { for (;;) {} }','--check','termination','--states','1',status='unknown',code=3)
        self.assertIsNone(report['trace'])
        self.driver('int main(void) { return 0; }','--timeout','0.000001',status='unknown',code=3)
        report,_,_=self.driver('#include <assert.h>\nint main(void) { assert(0); }','--depth','0',status='holds_through_depth')
        self.assertEqual(report['depth'],0)
        self.assertEqual(report['unbounded_outcome'],'unknown')

    def test_induction_and_assertion_identity(self):
        report,_,_=self.driver('#include <assert.h>\nint main(void) { assert(1); assert(2); return 0; }',
                              '--prove','--depth','12',status='proven_for_model')
        self.assertTrue(report['backend']['proof']['verified'])
        source='declare void @__VERIFIER_assert(i32)\ndefine void @main() { call void @__VERIFIER_assert(i32 1)\ncall void @__VERIFIER_assert(i32 0)\nret void }'
        self.assertEqual(self.candidate(source),self.candidate(source))

    def test_unsupported_c_and_disabled_assertions_never_publish(self):
        for source, options in [('#include <assert.h>\nint main(void) { assert(0); }',['-D','NDEBUG']),
                                ('#define NDEBUG\n#include <assert.h>\nint main(void) { assert(0); }',[]),
                                ('int main(void) { int a[2]={0,1}; return a[1]; }',[]),
                                ('int main(void) { return missing(); }',[])]:
            with self.subTest(source=source):
                _,destination,_=self.driver(source,*options,status='error',code=2)
                self.assertFalse(destination.exists())


if __name__=='__main__': unittest.main()
