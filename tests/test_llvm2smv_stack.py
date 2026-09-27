#!/usr/bin/env python3
"""Bounded call frames, recursion, dynamic objects, and resource evidence."""
import subprocess
import unittest
import test_llvm2smv_memory as memory
from test_llvm2smv_scalar import BINARY, CLANG, HEADER, ROOT, prop, symbol

class StackTests(unittest.TestCase):
    setUp=memory.MemoryTests.setUp
    candidate=memory.MemoryTests.candidate
    bundle=memory.MemoryTests.bundle
    query=memory.MemoryTests.query
    reach=memory.MemoryTests.reach
    returned=memory.MemoryTests.returned
    report=memory.MemoryTests.report
    driver=memory.MemoryTests.driver
    def test_recursive_registers_and_depth(self):
        source='''define i8 @sum(i8 %n) {
 %zero=icmp eq i8 %n,0
 br i1 %zero,label %base,label %recurse
base: ret i8 0
recurse: %prev=sub i8 %n,1
 %r=call i8 @sum(i8 %prev)
 %v=add i8 %n,%r
 ret i8 %v }
define i8 @main() { %r=call i8 @sum(i8 3)
 ret i8 %r }'''
        model=self.bundle(source,('--stack-depth=5',))
        self.returned(model,6,depth=40)
        self.assertEqual(self.reach(model,'!'+prop('stack_within_bound'),40)['outcome'],'unreachable')
        model=self.bundle(source,('--stack-depth=4',))
        report=self.report(model,35)
        self.assertEqual(report['status'],'resource_bound_reached')
        self.assertEqual(report['failure_kind'],'stack_depth_bound')
        self.assertEqual(report['replay']['outcome'],'valid')
        self.assertEqual(len(report['source_trace']['frames'][-2]['call_stack']),4)
    def test_recursive_entry_is_not_expanded_from_mutated_body(self):
        model=self.bundle('define i8 @main() { %v=call i8 @main()\nret i8 %v }',('--stack-depth=3',))
        self.assertEqual(self.reach(model,'!'+prop('stack_within_bound'),6)['outcome'],'reachable')
        self.assertEqual(self.reach(model,prop('terminated'),8)['outcome'],'unreachable')
    def test_mutual_recursion(self):
        model=self.bundle('''define i1 @even(i8 %n) { %z=icmp eq i8 %n,0
 br i1 %z,label %base,label %next
base: ret i1 true
next: %m=sub i8 %n,1
 %r=call i1 @odd(i8 %m)
 ret i1 %r }
define i1 @odd(i8 %n) { %z=icmp eq i8 %n,0
 br i1 %z,label %base,label %next
base: ret i1 false
next: %m=sub i8 %n,1
 %r=call i1 @even(i8 %m)
 ret i1 %r }
define i1 @main() { %r=call i1 @even(i8 3)
 ret i1 %r }''',('--stack-depth=5',))
        self.returned(model,0,depth=35)
    def test_recursive_local_objects(self):
        model=self.bundle('''define i8 @sum(i8 %n) {
 %a=alloca i8,align 1
 %p=getelementptr i8,ptr %a,i64 0
 store i8 %n,ptr %p,align 1
 %z=icmp eq i8 %n,0
 br i1 %z,label %base,label %next
base: ret i8 0
next: %m=sub i8 %n,1
 %r=call i8 @sum(i8 %m)
 %v=load i8,ptr %p,align 1
 %s=add i8 %r,%v
 ret i8 %s }
define i8 @main() { %r=call i8 @sum(i8 1)
 ret i8 %r }''',('--stack-depth=3','--memory-bytes=2'))
        self.returned(model,1,depth=30)
    def test_dynamic_extent_and_capacity(self):
        body='''define i8 @main() {
 %n=add i8 1,1
 %a=alloca i8,i8 %n,align 1
 %p=getelementptr i8,ptr %a,i64 INDEX
 store i8 7,ptr %p,align 1
 %v=load i8,ptr %p,align 1
 ret i8 %v }'''
        model=self.bundle(body.replace('INDEX','1'),('--dynamic-stack-bytes=2',))
        self.returned(model,7)
        model=self.bundle(body.replace('INDEX','2'),('--dynamic-stack-bytes=4',))
        self.assertEqual(self.reach(model,prop('runtime_error'),8)['outcome'],'reachable')
        model=self.bundle(body.replace('INDEX','1'),('--dynamic-stack-bytes=1',))
        report=self.report(model,8)
        self.assertEqual(report['status'],'resource_bound_reached')
        self.assertEqual(report['failure_kind'],'stack_allocation_capacity')
    def test_repeated_alloca_does_not_reclaim_live_objects(self):
        model=self.bundle('''define void @main() { br label %loop
loop: %a=alloca [1 x i8],align 1
 br label %loop }''')
        self.assertEqual(self.report(model,6)['failure_kind'],'stack_allocation_capacity')
    def test_stack_restore_expires_dynamic_object(self):
        model=self.bundle('''declare ptr @llvm.stacksave.p0()
declare void @llvm.stackrestore.p0(ptr)
define i8 @main() {
 %s=call ptr @llvm.stacksave.p0()
 %n=add i8 1,1
 %a=alloca i8,i8 %n,align 1
 store i8 7,ptr %a,align 1
 call void @llvm.stackrestore.p0(ptr %s)
 %v=load i8,ptr %a,align 1
 ret i8 %v }''',('--dynamic-stack-bytes=2',))
        self.assertEqual(self.reach(model,prop('runtime_error'),10)['outcome'],'reachable')
    def test_c_vla(self):
        report,_,_=self.driver(ROOT/'tests/llvm2smv/stack/vla.c',
                              '--memory-bytes','2','--dynamic-stack-bytes','2','--depth','30','--timeout','120',status='holds_through_depth')
        self.assertEqual(report['call_stack_policy']['depth_limit'],8)
        self.native('vla',0)
        self.native('vla',1)
    def native(self,name,pick=0):
        runtime=self.path/'runtime.c'
        runtime.write_text(f'#include <stdlib.h>\n_Bool __VERIFIER_nondet_bool(void) {{ return {pick}; }}\nvoid __VERIFIER_assert(int x) {{ if(!x) exit(42); }}\n')
        executable=self.path/'native'
        subprocess.run([CLANG,'-O0','-I',str(ROOT/'llvm2smv/runtime'),str(ROOT/f'tests/llvm2smv/stack/{name}.c'),str(runtime),'-o',str(executable)],capture_output=True,check=True,timeout=30)
        self.assertEqual(subprocess.run([str(executable)],timeout=5).returncode,0)
    def test_c_recursive_call_and_depth_evidence(self):
        path=ROOT/'tests/llvm2smv/stack/recursive.c'
        self.driver(path,'--stack-depth','3','--depth','30',status='holds_through_depth')
        report,_,_=self.driver(path,'--stack-depth','2','--depth','20',status='resource_bound_reached',code=3)
        self.assertEqual(report['failure_kind'],'stack_depth_bound')
        self.assertEqual(report['replay']['outcome'],'valid')
        self.assertEqual([f['function'] for f in report['source_trace']['frames'][-2]['call_stack']],['main','flip'])
        self.native('recursive')
    def test_termination_depth_bound_is_not_nontermination(self):
        report,_,_=self.driver('static void f(void) { f(); }\nint main(void) { f(); return 0; }',
                              '--stack-depth','2','--check','termination',status='resource_bound_reached',code=3)
        self.assertEqual(report['failure_kind'],'stack_depth_bound')
        self.assertEqual(report['replay']['outcome'],'valid')
    def test_aggregate_arguments_results_and_noundef(self):
        model=self.bundle("""define noundef {i8,i8} @pair({i8,i8} noundef %arg) {
 %x=extractvalue {i8,i8} %arg,0
 %y=add i8 %x,1
 %r=insertvalue {i8,i8} %arg,i8 %y,1
 ret {i8,i8} %r }
define i8 @main() { %r=call {i8,i8} @pair({i8,i8} {i8 6,i8 0})
 %v=extractvalue {i8,i8} %r,1
 ret i8 %v }""")
        self.returned(model,7,depth=15)
    def test_cutoff_does_not_hide_unsupported_callee(self):
        self.candidate('''declare void @unknown()
define void @f() { call void @unknown()
 call void @f()
 ret void }
define void @main() { call void @f()
 ret void }''',ok=False)

    def test_restore_preserves_earlier_objects_and_releases_capacity(self):
        model=self.bundle('''declare ptr @llvm.stacksave.p0()
declare void @llvm.stackrestore.p0(ptr)
define i8 @main() {
 %a=alloca [1 x i8],align 1
 store i8 7,ptr %a,align 1
 br label %loop
loop:
 %again=phi i1 [true,%0],[false,%loop]
 %s=call ptr @llvm.stacksave.p0()
 %n=add i8 0,1
 %b=alloca i8,i8 %n,align 1
 store i8 2,ptr %b,align 1
 call void @llvm.stackrestore.p0(ptr %s)
 br i1 %again,label %loop,label %exit
exit:
 %v=load i8,ptr %a,align 1
 ret i8 %v }''',('--memory-bytes=2','--dynamic-stack-bytes=1'))
        self.returned(model,7,depth=22)

    def test_stale_dynamic_generation_is_not_reinterpreted(self):
        body='''declare ptr @llvm.stacksave.p0()
declare void @llvm.stackrestore.p0(ptr)
define i8 @main() { br label %loop
loop:
 %again=phi i1 [true,%0],[false,%loop]
 %old=phi ptr [null,%0],[%a,%loop]
 %s=call ptr @llvm.stacksave.p0()
 %n=or i1 true,false
 %a=alloca i8,i1 %n,align 1
 store i8 7,ptr %a,align 1
 call void @llvm.stackrestore.p0(ptr %s)
 br i1 %again,label %loop,label %exit
exit:
 OPERATION
 ret i8 0 }'''
        for instruction,property_name in [('load i8,ptr %old,align 1','runtime_error'),
                ('getelementptr inbounds i8,ptr %old,i64 1','memory_supported')]:
            model=self.bundle(body.replace('OPERATION','%v='+instruction),('--memory-bytes=1','--dynamic-stack-bytes=1'))
            target=prop(property_name) if property_name=='runtime_error' else '!'+prop(property_name)
            self.assertEqual(self.reach(model,target,17)['outcome'],'reachable')

    def test_stack_token_and_abi_rejections(self):
        for source in [
            '''declare ptr @llvm.stacksave.p0()
define i1 @main() { %s=call ptr @llvm.stacksave.p0()
 %b=icmp eq ptr %s,null
 ret i1 %b }''',
            '''declare ptr @llvm.stacksave.p0()
declare void @llvm.stackrestore.p0(ptr)
define void @restore(ptr %p) { call void @llvm.stackrestore.p0(ptr %p)
 ret void }
define void @main() { %s=call ptr @llvm.stacksave.p0()
 call void @restore(ptr %s)
 ret void }''',
            '''define void @f(ptr byval(i8) %p) { ret void }
define void @main() { %a=alloca i8
 call void @f(ptr byval(i8) %a)
 ret void }''']:
            self.candidate(source,ok=False)

    def test_aggregate_noundef_and_depth_limits(self):
        model=self.bundle('''define void @f({i8,i8} noundef %p) { ret void }
define void @main() { call void @f({i8,i8} {i8 0,i8 poison})
 ret void }''')
        self.assertEqual(self.reach(model,prop('runtime_error'),5)['outcome'],'reachable')
        for flag in ('--stack-depth=0','--stack-depth=65','--dynamic-stack-bytes=0','--dynamic-stack-bytes=4097'):
            path=self.path/'limits.ll'; path.write_text(HEADER+'define void @main() { ret void }')
            result=subprocess.run([BINARY,'--emit-scalar-bundle',flag,str(path)],capture_output=True,text=True,timeout=10)
            self.assertEqual(result.returncode,2,result.stderr)
            self.assertEqual(result.stdout,'')

    def test_frame_identity_and_rejected_function_addresses(self):
        source='define i1 @main() { %r=call i1 @main()\nret i1 %r }'
        self.assertEqual(self.candidate(source),self.candidate(source))
        self.candidate('define ptr @f() { ret ptr @f }\ndefine void @main() { %p=call ptr @f()\nret void }',ok=False)

    def test_zero_and_poison_dynamic_counts(self):
        for count,status in [('0','unsupported'),('poison','violation')]:
            model=self.bundle(f'''define i8 @main() {{
 %n=add i8 0,{count}
 %a=alloca i8,i8 %n,align 1
 ret i8 0 }}''',('--memory-bytes=1','--dynamic-stack-bytes=1'))
            report=self.report(model,4)
            self.assertEqual(report['status'],status)
            self.assertEqual(report['failure_kind'],'unsupported_memory_operation' if count=='0' else 'runtime_error')
            self.assertEqual(report['replay']['outcome'],'valid')

if __name__=='__main__': unittest.main()
