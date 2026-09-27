#!/usr/bin/env python3
"""M4 byte/provenance semantics and native replay, with independent byte oracles."""
import json
from pathlib import Path
import subprocess
import sys
import unittest
from types import SimpleNamespace
import test_llvm2smv_c as workflow
import test_llvm2smv_scalar as scalar
from test_llvm2smv_scalar import ROOT, BINARY, CHECKER, HEADER, prop, symbol
sys.path.insert(0,str(ROOT/'tools'))
from llvm2smv_artifact import publish, read_json
from llvm2smv_c import check


class MemoryTests(unittest.TestCase):
    setUp=scalar.ScalarTests.setUp
    candidate=scalar.ScalarTests.candidate
    driver=workflow.CWorkflowTests.driver
    query=scalar.ScalarTests.query
    reach=scalar.ScalarTests.reach
    def bundle(self,source,options=()):
        self.serial+=1; path=self.path/f'memory-{self.serial}.ll'; path.write_text(HEADER+source)
        p=subprocess.run([BINARY,'--emit-scalar-bundle','--diagnostics=json',*options,str(path)],capture_output=True,text=True,timeout=30)
        self.assertEqual(p.returncode,0,p.stderr)
        return publish(read_json(p.stdout),self.path/f'bundle-{self.serial}',CHECKER,timeout=90)
    def returned(self,model,value,width=8,depth=12):
        r=self.reach(model,prop('terminated'),depth)
        self.assertEqual(r['outcome'],'reachable',r)
        self.assertEqual(r['trace']['steps'][-1]['values'][symbol('return')],str(value))
        self.assertEqual(self.query(model,'validate-trace',trace=r['trace'])['outcome'],'valid')
        return r
    def test_partial_writes_and_little_endian_aliases(self):
        model=self.bundle('''@g=global i16 4660, align 2
define i16 @main() {
 %p=getelementptr i8, ptr @g,i64 1
 store i8 86,ptr %p,align 1
 %v=load i16,ptr @g,align 2
 ret i16 %v
}''')
        expected=bytearray((0x1234).to_bytes(2,'little')); expected[1]=86
        self.returned(model,int.from_bytes(expected,'little'),16)
    def test_aggregate_layout_insert_extract_and_padding(self):
        model=self.bundle('''%S=type {i8,i16}
@g=global %S {i8 3,i16 9},align 2
define i16 @main() {
 %s=load %S,ptr @g,align 2
 %u=insertvalue %S %s,i16 513,1
 store %S %u,ptr @g,align 2
 %p=getelementptr %S,ptr @g,i64 0,i32 1
 %r=load i16,ptr %p,align 2
 ret i16 %r
}''')
        self.returned(model,513,16)
        # Aggregate admission must precede mem2reg, including unused objects.
        model=self.bundle('define i8 @main() { %a=alloca [2 x i8],align 1\nret i8 7 }')
        self.returned(model,7)
    def test_dynamic_array_index_and_pointer_select(self):
        model=self.bundle('''@g=global [2 x i8] [i8 3,i8 4],align 1
declare i1 @__VERIFIER_nondet_bool()
define i8 @main() {
 %b=call i1 @__VERIFIER_nondet_bool()
 %i=zext i1 %b to i64
 %p=getelementptr inbounds [2 x i8],ptr @g,i64 0,i64 %i
 %q=select i1 %b,ptr %p,ptr @g
 %r=load i8,ptr %q,align 1
 ret i8 %r
}''')
        for n in (3,4): self.assertEqual(self.reach(model,f'{prop("terminated")} && {symbol("return")}=(uint8){n}',9)['outcome'],'reachable')
        self.assertEqual(self.reach(model,prop('runtime_error'),9)['outcome'],'unreachable')
    def test_memmove_overlap_and_memcpy_self(self):
        for operation,offset in [('memmove',1),('memcpy',0)]:
            model=self.bundle(f'''@g=global [3 x i8] [i8 1,i8 2,i8 3],align 1
declare void @llvm.{operation}.p0.p0.i64(ptr,ptr,i64,i1)
define i8 @main() {{
 %p=getelementptr i8,ptr @g,i64 {offset}
 call void @llvm.{operation}.p0.p0.i64(ptr %p,ptr @g,i64 2,i1 false)
 %q=getelementptr i8,ptr @g,i64 2
 %r=load i8,ptr %q,align 1
 ret i8 %r
}}''')
            self.returned(model,2 if offset else 3)
    def test_memcpy_overlap_fault_and_zero_length(self):
        model=self.bundle('''@g=global [3 x i8] zeroinitializer,align 1
declare void @llvm.memcpy.p0.p0.i64(ptr,ptr,i64,i1)
define void @main() {
 %p=getelementptr i8,ptr @g,i64 1
 call void @llvm.memcpy.p0.p0.i64(ptr %p,ptr @g,i64 2,i1 false)
 ret void
}''')
        self.assertEqual(self.reach(model,prop('runtime_error'),4)['outcome'],'reachable')
        model=self.bundle('''declare void @llvm.memcpy.p0.p0.i64(ptr,ptr,i64,i1)
define i8 @main() { call void @llvm.memcpy.p0.p0.i64(ptr null,ptr poison,i64 0,i1 false)
 ret i8 7 }''')
        self.returned(model,7)
    def test_bounds_alignment_readonly_and_uninitialized(self):
        bodies=[
            '@g=global [2 x i8] zeroinitializer,align 2\ndefine i8 @main() { %p=getelementptr [2 x i8],ptr @g,i64 0,i64 2\n%v=load i8,ptr %p,align 1\nret i8 %v }',
            '@g=global [4 x i8] zeroinitializer,align 2\ndefine i16 @main() { %p=getelementptr i8,ptr @g,i64 1\n%v=load i16,ptr %p,align 2\nret i16 %v }',
            '@g=global [1 x i8] zeroinitializer,align 1\ndefine i8 @main() { %v=load i8,ptr @g,align 4294967296\nret i8 %v }',
            '@g=constant [1 x i8] zeroinitializer,align 1\ndefine i8 @main() { store i8 1,ptr @g,align 1\nret i8 0 }',
            'define i8 @main() { %a=alloca [1 x i8],align 1\n%p=getelementptr [1 x i8],ptr %a,i64 0,i64 0\n%v=load i8,ptr %p,align 1\nret i8 %v }',
            'define i8 @main() { %a=alloca [1 x i8],align 1\nstore i1 true,ptr %a,align 1\n%v=load i8,ptr %a,align 1\nret i8 %v }',
        ]
        for body in bodies:
            model=self.bundle(body)
            self.assertEqual(self.reach(model,prop('runtime_error'),6)['outcome'],'reachable')
    def test_lifetime_end_and_escaping_stack_pointer(self):
        model=self.bundle('''declare void @llvm.lifetime.start.p0(i64,ptr)
declare void @llvm.lifetime.end.p0(i64,ptr)
define i8 @main() {
 %a=alloca i8,align 1
 call void @llvm.lifetime.start.p0(i64 1,ptr %a)
 store i8 7,ptr %a,align 1
 call void @llvm.lifetime.end.p0(i64 1,ptr %a)
 %v=load i8,ptr %a,align 1
 ret i8 %v
}''')
        self.assertEqual(self.reach(model,prop('runtime_error'),8)['outcome'],'reachable')
        model=self.bundle('''define ptr @f() { %a=alloca i8,align 1
 store i8 3,ptr %a,align 1
 ret ptr %a }
define i8 @main() { %p=call ptr @f()
 %v=load i8,ptr %p,align 1
 ret i8 %v }''')
        self.assertEqual(self.reach(model,prop('runtime_error'),10)['outcome'],'reachable')
    def test_lifetime_start_is_required_before_access(self):
        model=self.bundle("""declare void @llvm.lifetime.start.p0(i64,ptr)
define i8 @main() {
 %a=alloca i8,align 1
 store i8 3,ptr %a,align 1
 call void @llvm.lifetime.start.p0(i64 1,ptr %a)
 ret i8 0
}""")
        self.assertEqual(self.reach(model,prop('runtime_error'),5)['outcome'],'reachable')
        self.assertEqual(self.reach(model,prop('terminated'),5)['outcome'],'unreachable')
    def test_pointer_aggregate_and_call_return_phi(self):
        model=self.bundle("""%S=type {ptr,i8}
@g=global i8 7,align 1
@s=global %S {ptr @g,i8 4},align 8
define ptr @address() { %s=load %S,ptr @s,align 8
 %p=extractvalue %S %s,0
 ret ptr %p }
define i8 @main() { %p=call ptr @address()
 %v=load i8,ptr %p,align 1
 ret i8 %v }
""")
        self.returned(model,7)
    def test_pointer_call_definedness_without_memory_access(self):
        for value in ('@g','poison'):
            model=self.bundle(f"""@g=global i8 3,align 1
define i8 @f(ptr noundef %p) {{ ret i8 7 }}
define i8 @main() {{ %v=call i8 @f(ptr {value})
 ret i8 %v }}""")
            if value=='poison':
                self.assertEqual(self.reach(model,prop('runtime_error'),8)['outcome'],'reachable')
            else: self.returned(model,7)
    def test_pointer_relocations_and_copy_tags(self):
        model=self.bundle('''@g=global i8 7,align 1
@a=global ptr @g,align 8
@b=global ptr null,align 8
declare void @llvm.memcpy.p0.p0.i64(ptr,ptr,i64,i1)
define i8 @main() {
 call void @llvm.memcpy.p0.p0.i64(ptr @b,ptr @a,i64 8,i1 false)
 %p=load ptr,ptr @b,align 8
 %v=load i8,ptr %p,align 1
 ret i8 %v
}''')
        self.returned(model,7,depth=8)
    def test_pointer_byte_edits_do_not_forge_provenance(self):
        model=self.bundle('''@g=global i8 7,align 1
@p=global ptr @g,align 8
define i8 @main() {
 %b=getelementptr i8,ptr @p,i64 1
 store i8 0,ptr %b,align 1
 %q=load ptr,ptr @p,align 8
 %v=load i8,ptr %q,align 1
 ret i8 %v
}''')
        self.assertEqual(self.reach(model,prop('runtime_error'),8)['outcome'],'reachable')
    def report(self,model,depth):
        self.serial+=1; temporary=self.path/f'check-{self.serial}'; temporary.mkdir()
        return check(SimpleNamespace(checker=CHECKER,timeout=60,check='safety',prove=False,depth=depth),model,temporary)
    def test_memset_zero_pointer_and_poison_fill(self):
        model=self.bundle("""@p=global ptr null,align 8
@g=global i8 7,align 1
declare void @llvm.memset.p0.i64(ptr,i8,i64,i1)
define i1 @main() {
 store ptr @g,ptr @p,align 8
 call void @llvm.memset.p0.i64(ptr @p,i8 0,i64 8,i1 false)
 %v=load ptr,ptr @p,align 8
 %c=icmp eq ptr %v,null
 ret i1 %c
}""")
        self.returned(model,1)
        model=self.bundle("""@g=global [1 x i8] zeroinitializer,align 1
declare void @llvm.memset.p0.i64(ptr,i8,i64,i1)
define i8 @main() {
 call void @llvm.memset.p0.i64(ptr @g,i8 poison,i64 1,i1 false)
 %v=load i8,ptr @g,align 1
 ret i8 %v
}""")
        r=self.reach(model,prop('terminated'),5)
        self.assertEqual(r['outcome'],'reachable')
        self.assertEqual(r['trace']['steps'][-1]['values'][symbol('return.poison')],True)
    def test_gep_one_past_negative_and_offset_coverage(self):
        model=self.bundle("""@g=global [2 x i8] [i8 3,i8 4],align 1
define i8 @main() {
 %end=getelementptr inbounds [2 x i8],ptr @g,i64 0,i64 2
 %last=getelementptr inbounds i8,ptr %end,i64 -1
 %v=load i8,ptr %last,align 1
 ret i8 %v
}""")
        self.returned(model,4)
        model=self.bundle("""@g=global [1 x i8] zeroinitializer,align 1
define void @main() { %p=getelementptr i8,ptr @g,i64 256
 ret void }""")
        report=self.report(model,4)
        self.assertEqual(report['status'],'unsupported')
        self.assertEqual(report['replay']['outcome'],'valid')
        self.assertEqual(self.reach(model,prop('runtime_error'),4)['outcome'],'unreachable')
        model=self.bundle("""@g=global [1 x i8] zeroinitializer,align 1
define i8 @main() { %p=getelementptr inbounds i8,ptr @g,i64 256
 %v=load i8,ptr %p,align 1
 ret i8 %v }""")
        self.assertEqual(self.reach(model,prop('runtime_error'),5)['outcome'],'reachable')
    def test_full_width_gep_wrap_and_inbounds_poison(self):
        for flag in ('','inbounds'):
            model=self.bundle(f"""@g=global [2 x i8] [i8 7,i8 8],align 1
define i8 @main() {{
 %p=getelementptr {flag} [2 x i8],ptr @g,i64 -9223372036854775808
 %v=load i8,ptr %p,align 1
 ret i8 %v
}}""")
            if flag:
                self.assertEqual(self.reach(model,prop('runtime_error'),5)['outcome'],'reachable')
            else: self.returned(model,7)
    def test_pointer_comparison_and_representation_coverage(self):
        model=self.bundle("""@g=global i8 3,align 1
@h=global i8 4,align 1
define i1 @main() { %eq=icmp eq ptr @g,@h
 ret i1 %eq }""")
        self.assertEqual(self.report(model,4)['status'],'unsupported')
        model=self.bundle("""@g=global i8 3,align 1
@p=global ptr @g,align 8
define i8 @main() { %v=load i8,ptr @p,align 1
 ret i8 %v }""")
        self.assertEqual(self.report(model,4)['status'],'unsupported')
        model=self.bundle("""@g=global i16 4660,align 2
define i8 @main() { store i8 86,ptr @g,align 1
 %v=load i8,ptr @g,align 1
 ret i8 %v }""")
        self.returned(model,86)
    def test_memory_admission_rejections(self):
        sources=[
            'define void @main() { %x=load {},ptr null,align 1\nret void }',
            'define void @main() { store {} zeroinitializer,ptr null,align 1\nret void }',
            'define void @main() { %a=alloca inalloca i8\nret void }',
            '@g=global [2 x i8] zeroinitializer\n@p=global ptr getelementptr inbounds ([2 x i8],ptr @g,i64 0,inrange i64 1)\ndefine void @main() { ret void }',
            'declare void @llvm.memcpy.p0.p0.i64(ptr,ptr,i64,i1)\ndefine void @main() { call void @llvm.memcpy.p0.p0.i64(ptr nonnull null,ptr null,i64 0,i1 false)\nret void }',
            '@g=global [129 x i8] zeroinitializer\ndefine void @main() { ret void }',
            '@g=global i8 1\ndefine i64 @main() { %n=ptrtoint ptr @g to i64\nret i64 %n }',
            '@g=global [1 x i8] zeroinitializer\ndefine i8 @main() { %v=load volatile i8,ptr @g\nret i8 %v }',
            '@g=global [1 x i8] zeroinitializer\ndefine i8 @main() { %v=load atomic i8,ptr @g seq_cst,align 1\nret i8 %v }',
        ]
        for source in sources:
            with self.subTest(source=source): self.candidate(source,ok=False)
    def test_c_alias_workflow_and_source_memory(self):
        source=ROOT/'tests/llvm2smv/memory/alias.c'
        self.driver(source,'--depth','30',status='holds_through_depth')
        text=source.read_text().replace('data[1] == 7','data[1] == 8')
        report,_,_=self.driver(text,'--depth','30',status='violation',code=1)
        self.assertEqual(report['replay']['outcome'],'valid')
        self.assertTrue(report['memory_policy']['objects'])
        self.assertTrue(report['source_trace']['frames'][-1]['memory'])
        runtime=self.path/'runtime.c'; runtime.write_text('#include <stdlib.h>\nvoid __VERIFIER_assert(int x) { if (!x) exit(42); }')
        for name,body,code in [('safe',source.read_text(),0),('unsafe',text,42)]:
            c=self.path/f'{name}.c'; c.write_text(body); exe=self.path/name
            subprocess.run([scalar.CLANG,'-O0','-I',str(ROOT/'llvm2smv/runtime'),str(c),str(runtime),'-o',str(exe)],check=True,capture_output=True)
            self.assertEqual(subprocess.run([str(exe)]).returncode,code)
    def test_allocation_generation_bound(self):
        model=self.bundle('''define i8 @touch(ptr %p) { %v=load i8,ptr %p,align 1
 ret i8 %v }
define i8 @f() { %a=alloca i8,align 1
 store i8 3,ptr %a,align 1
 %v=call i8 @touch(ptr %a)
 ret i8 %v }
define i8 @main() { br label %loop
loop: %n=phi i1 [false,%0],[true,%loop]
 %v=call i8 @f()
 br i1 %n,label %exit,label %loop
exit: ret i8 %v }''',('--allocation-generations=1',))
        self.assertEqual(self.reach(model,'!'+prop('memory_within_bound'),22)['outcome'],'reachable')
        self.assertEqual(self.reach(model,prop('terminated'),22)['outcome'],'unreachable')
        report=self.report(model,22)
        self.assertEqual(report['status'],'resource_bound_reached')
        self.assertEqual(report['replay']['outcome'],'valid')

if __name__=='__main__': unittest.main()
