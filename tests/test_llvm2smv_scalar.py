#!/usr/bin/env python3
"""M2 scalar LLVM semantics checked against a separate small integer oracle."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from llvm2smv_artifact import publish, read_json
BINARY = os.environ.get('LLVM2SMV', str(ROOT / 'llvm2smv/llvm2smv'))
CHECKER = os.environ.get('YASMV', str(ROOT / 'yasmv'))
CLANG = os.environ.get('CLANG', 'clang-18')
os.environ.setdefault('YASMV_HOME', str(ROOT))
HEADER = 'source_filename = "scalar-fixture"\ntarget triple = "x86_64-unknown-linux-gnu"\ntarget datalayout = "e-p:64:64-i64:64-n8:16:32:64-S128"\n'


def symbol(key): return 'v_' + key.encode().hex()
def prop(key): return 'p_' + key.encode().hex()
DONE, ERROR = prop('terminated'), prop('runtime_error')
RETURN, POISON = symbol('return'), symbol('return.poison')


def oracle(op, a, b, width, flag=''):
    """Mathematical integers; no shared code or APInt dependency with lowering."""
    mask = (1 << width) - 1
    lo, hi = -(1 << (width-1)), (1 << (width-1))-1
    signed = lambda n: n if n <= hi else n - (1 << width)
    sa, sb = signed(a), signed(b)
    poison, error, value = False, False, 0
    if op in ('add', 'sub', 'mul'):
        math = {'add': lambda x,y:x+y, 'sub': lambda x,y:x-y, 'mul': lambda x,y:x*y}[op]
        value = math(a,b)
        if 'nuw' in flag: poison |= not 0 <= value <= mask
        if 'nsw' in flag: poison |= not lo <= math(sa,sb) <= hi
    elif op in ('and', 'or', 'xor'):
        value = {'and': a&b, 'or': a|b, 'xor': a^b}[op]
        poison = flag == 'disjoint' and bool(a&b)
    elif op in ('shl', 'lshr', 'ashr'):
        poison = b >= width
        if not poison:
            value = (a << b) if op=='shl' else (sa >> b) if op=='ashr' else (a >> b)
            if 'nuw' in flag: poison |= a << b > mask
            if 'nsw' in flag: poison |= not lo <= sa << b <= hi
            if flag == 'exact': poison |= bool(a & ((1 << b)-1))
    elif op in ('udiv', 'urem', 'sdiv', 'srem'):
        error = b==0 or (op.startswith('s') and sa==lo and sb==-1)
        if not error:
            x,y = (sa,sb) if op.startswith('s') else (a,b)
            q = abs(x)//abs(y)
            if (x<0) != (y<0): q = -q
            r = x-q*y
            value = r if op.endswith('rem') else q
            poison = flag=='exact' and r!=0
    else: raise AssertionError(op)
    return value & mask, poison, error


class ScalarTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name); self.serial=0

    def candidate(self, source, entry='main', ok=True):
        self.serial += 1
        path=self.path/f'input-{self.serial}.ll'; path.write_text(HEADER+source)
        p=subprocess.run([BINARY,'--emit-scalar-bundle','--diagnostics=json','--entry='+entry,str(path)],
                         capture_output=True,text=True,timeout=30)
        if not ok:
            self.assertEqual(p.returncode,2,p.stdout+p.stderr); self.assertEqual(p.stdout,'')
            self.assertIn(json.loads(p.stderr)['status'], ('unsupported','error'))
            return
        self.assertEqual(p.returncode,0,p.stderr)
        return read_json(p.stdout)

    def bundle(self, source, entry='main'):
        artifact=self.candidate(source,entry)
        return publish(artifact,self.path/f'bundle-{self.serial}',CHECKER,timeout=60)

    def query(self, model, operation='reach', **extra):
        path=self.path/'query.json'
        path.write_text(json.dumps(dict(version=1,model=str(model/'model.smv'),query=dict(operation=operation,**extra))))
        p=subprocess.run([CHECKER,'--quiet','--query-file',str(path)],capture_output=True,text=True,timeout=180)
        self.assertEqual(p.returncode,0,p.stdout+p.stderr)
        return json.loads(p.stdout)

    def reach(self, model, target, depth):
        return self.query(model,target=target,limits={'depth':depth})

    def compile_c(self, path, entry='main'):
        self.serial += 1; ir=self.path/f'compiled-{self.serial}.ll'
        subprocess.run([CLANG,'-S','-emit-llvm','-O0','-g','-fno-finite-loops',str(path),'-o',str(ir)],check=True,capture_output=True)
        p=subprocess.run([BINARY,'--emit-scalar-bundle','--diagnostics=json','--entry='+entry,str(ir)],capture_output=True,text=True,timeout=30)
        self.assertEqual(p.returncode,0,p.stderr)
        return publish(read_json(p.stdout),self.path/f'compiled-bundle-{self.serial}',CHECKER,timeout=60)

    def test_counter(self):
        model=self.compile_c(ROOT/'llvm2smv/examples/simple/counter.c')
        counter=symbol('global.counter')
        r=self.reach(model,DONE,90)
        self.assertEqual(r['outcome'],'reachable')
        self.assertEqual(r['trace']['steps'][-1]['values'][counter],'10')
        self.assertEqual(self.reach(model,f'{counter}=(uint32)99 || {ERROR}',95)['outcome'],'unreachable')
        self.assertEqual(self.query(model,'validate-trace',trace=r['trace'])['outcome'],'valid')

    def test_conditionals_nested_loops_and_nontermination(self):
        for entry, expected, depth in [('conditional',5,20),('nested',sum(i*4+j for i in range(3) for j in range(4)),250)]:
            with self.subTest(entry=entry):
                model=self.compile_c(ROOT/'tests/llvm2smv/scalar/loops.c',entry)
                r=self.reach(model,DONE,depth); self.assertEqual(r['outcome'],'reachable')
                self.assertEqual(r['trace']['steps'][-1]['values'][RETURN],str(expected))
                if entry=='conditional':
                    self.assertEqual(self.reach(model,f'{symbol("global.side")}=(uint32)99',len(r['trace']['steps'])+2)['outcome'],'unreachable')
                self.assertEqual(self.reach(model,f'{ERROR} || ({DONE} && {RETURN}!=(uint32){expected})',len(r['trace']['steps'])+2)['outcome'],'unreachable')
        model=self.compile_c(ROOT/'tests/llvm2smv/scalar/loops.c','endless')
        self.assertEqual(self.reach(model,f'{DONE} || {ERROR}',12)['outcome'],'unreachable')
        self.assertEqual(self.query(model,'check-trans',limits={'depth':12})['outcome'],'satisfiable')

    def test_phi_swap_and_switch(self):
        source='''define i8 @main() {
entry: br label %loop
loop:
  %a = phi i8 [1, %entry], [%b, %loop]
  %b = phi i8 [2, %entry], [%a, %loop]
  %n = phi i8 [0, %entry], [%next, %loop]
  %next = add i8 %n, 1
  %more = icmp ult i8 %n, 3
  br i1 %more, label %loop, label %exit
exit:
  %t = mul i8 %a, 10
  %r = add i8 %t, %b
  switch i8 %r, label %bad [i8 21, label %good i8 22, label %bad]
good: ret i8 %r
bad: ret i8 99
}'''
        model=self.bundle(source)
        a,b=1,2
        for _ in range(3): a,b=b,a
        expected=a*10+b
        self.assertEqual(self.reach(model,f'{DONE} && {RETURN}=(uint8){expected}',20)['outcome'],'reachable')
        self.assertEqual(self.reach(model,f'{ERROR} || ({DONE} && {RETURN}!=(uint8){expected})',24)['outcome'],'unreachable')

    def check_operator(self, op, flag='', width=2, multiplier=None):
        source=f'''@a = global i{width} 0, align 1
@b = global i{width} 0, align 1
define i{width} @main() {{
  %a = freeze i{width} poison
  %b = freeze i{width} poison
  store i{width} %a, ptr @a, align 1
  store i{width} %b, ptr @b, align 1
  %r = {op} {flag} i{width} %a, {'%b' if multiplier is None else multiplier}
  ret i{width} %r
}}'''
        model=self.bundle(source)
        failures=[]
        for a in range(1 << width):
            for b in range(1 << width):
                value,poison,error=oracle(op,a,b if multiplier is None else multiplier,width,flag)
                expected=ERROR if error else f'({DONE} && {POISON}={str(poison).upper()}' + (')' if poison else f' && {RETURN}=(uint{width}){value})')
                inputs=f'{symbol("global.a")}=(uint{width}){a} && {symbol("global.b")}=(uint{width}){b}'
                failures.append(f'({inputs} && !({expected}))')
        bad=f'({DONE} || {ERROR}) && ('+' || '.join(failures)+')'
        self.assertEqual(self.reach(model,bad,7)['outcome'],'unreachable', (op,flag,width))
        self.assertEqual(self.reach(model,f'{DONE} || {ERROR}',7)['outcome'],'reachable')

    def test_exhaustive_small_integer_semantics(self):
        for op in ('add','sub','mul','and','or','xor','shl','lshr','ashr','udiv','urem','sdiv','srem'):
            with self.subTest(op=op): self.check_operator(op)

    def test_exhaustive_flags_and_i1(self):
        for op,flag in [('add','nsw nuw'),('sub','nsw nuw'),('mul','nsw nuw'),('shl','nsw nuw'),
                        ('lshr','exact'),('ashr','exact'),('udiv','exact'),('sdiv','exact'),('or','disjoint')]:
            with self.subTest(op=op,flag=flag): self.check_operator(op,flag)
        for op in ('add','sub','mul','ashr','sdiv'):
            with self.subTest(op=op,width=1): self.check_operator(op,width=1)

    def test_constant_multiply_bounds(self):
        for constant in range(4):
            with self.subTest(constant=constant): self.check_operator('mul','nsw nuw',multiplier=constant)

    def test_comparison_predicates(self):
        for predicate in ('eq','ne','ult','ule','ugt','uge','slt','sle','sgt','sge'):
            source=f'''@a=global i2 0, align 1
@b=global i2 0, align 1
define i1 @main() {{
 %a=freeze i2 poison
 %b=freeze i2 poison
 store i2 %a, ptr @a, align 1
 store i2 %b, ptr @b, align 1
 %r=icmp {predicate} i2 %a, %b
 ret i1 %r
}}'''
            model=self.bundle(source)
            failures=[]
            for a in range(4):
                for b in range(4):
                    x,y=(a if a<2 else a-4,b if b<2 else b-4) if predicate.startswith('s') else (a,b)
                    condition={'eq':x==y,'ne':x!=y,'lt':x<y,'le':x<=y,'gt':x>y,'ge':x>=y}[predicate[-2:]]
                    failures.append(f'({symbol("global.a")}=(uint2){a} && {symbol("global.b")}=(uint2){b} && {RETURN}!=(uint1){int(condition)})')
            self.assertEqual(self.reach(model,f'{ERROR} || ({DONE} && ({POISON} || '+' || '.join(failures)+'))',6)['outcome'],'unreachable',predicate)
            self.assertEqual(self.reach(model,DONE,6)['outcome'],'reachable')

    def test_casts_comparisons_and_64bit_boundaries(self):
        source='''define i64 @main() {
  %n = add i64 9223372036854775807, 1
  %c = icmp slt i64 %n, 0
  %s = sext i1 %c to i64
  %z = zext i1 %c to i64
  %t = trunc i64 254 to i1
  %tz = zext i1 %t to i64
  %a = add i64 %s, %z
  %r = add i64 %a, %tz
  ret i64 %r
}'''
        model=self.bundle(source)
        self.assertEqual(self.reach(model,f'{DONE} && {RETURN}=(uint64)0 && !{POISON}',9)['outcome'],'reachable')
        self.assertEqual(self.reach(model,f'{DONE} && ({RETURN}!=(uint64)0 || {POISON})',10)['outcome'],'unreachable')
        for op,flags,a,b in [('add','nsw',9223372036854775807,1),('sub','nuw',0,1),('shl','nuw',1,63)]:
            value,poison,error=oracle(op,a,b,64,flags)
            model=self.bundle(f'define i64 @main() {{ %r = {op} {flags} i64 {a}, {b}\n ret i64 %r }}')
            condition=f'{DONE} && {POISON}={str(poison).upper()}'
            if not poison: condition += f' && {RETURN}=(uint64){value}'
            self.assertEqual(self.reach(model,condition,2)['outcome'],'reachable')

    def test_poison_selection_memory_freeze_and_uses(self):
        for condition,poison in [('false',False),('true',True)]:
            model=self.bundle(f'''define i8 @main() {{
 %p = add nsw i8 127, 1
 %r = select i1 {condition}, i8 %p, i8 7
 ret i8 %r
}}''')
            self.assertEqual(self.reach(model,f'{DONE} && {POISON}={str(poison).upper()}',3)['outcome'],'reachable')
            self.assertEqual(self.reach(model,ERROR,4)['outcome'],'unreachable')
        for source in ['define i8 @main() { br i1 poison, label %a, label %b\na: ret i8 1\nb: ret i8 0\n}',
                       'define noundef i8 @main() { ret i8 poison }',
                       'define i8 @main() { %r = udiv i8 1, poison\n ret i8 %r }',
                       'define i8 @main() { %r = sdiv i8 poison, -1\n ret i8 %r }',
                       'define i8 @main() { %r = srem i8 poison, -1\n ret i8 %r }',
                       'define i8 @main() { unreachable }']:
            model=self.bundle(source)
            self.assertEqual(self.reach(model,ERROR,2)['outcome'],'reachable')
            self.assertEqual(self.reach(model,DONE,3)['outcome'],'unreachable')
        model=self.bundle('''@g = global i8 0, align 1
define i1 @main() {
 store i8 poison, ptr @g, align 1
 %p = load i8, ptr @g, align 1
 %f = freeze i8 %p
 %c = icmp eq i8 %f, %f
 ret i1 %c
}''')
        self.assertEqual(self.reach(model,f'{DONE} && {RETURN}=(uint1)1 && !{POISON}',5)['outcome'],'reachable')
        self.assertEqual(self.reach(model,f'{ERROR} || ({DONE} && {RETURN}=(uint1)0)',6)['outcome'],'unreachable')

    def test_additional_poison_boundaries(self):
        for operation in ('udiv i8 poison, 2', 'sdiv i8 poison, 2', 'zext nneg i4 15 to i8'):
            model=self.bundle(f'define i8 @main() {{ %r = {operation}\n ret i8 %r }}')
            self.assertEqual(self.reach(model,f'{DONE} && {POISON}',2)['outcome'],'reachable')
            self.assertEqual(self.reach(model,ERROR,3)['outcome'],'unreachable')

    def test_preflight_and_normalization_rejections(self):
        cases=[
          'declare void @f()\ndefine i8 @main() { br i1 false, label %bad, label %ok\nbad: call void @f()\n ret i8 0\nok: ret i8 1 }',
          'define i8 @main() { %p=alloca i8\n %x=load i8, ptr %p\n ret i8 %x }',
          'define i8 @main() { ret i8 undef }',
          'define i8 @main() mustprogress { ret i8 0 }',
          'define i8 @main() willreturn { ret i8 0 }',
          'define i8 @main(i8 %x) { ret i8 %x }',
          'define i128 @main() { ret i128 0 }',
          '@g=global i8 0, align 1\ndefine i8 @main() { %x=load volatile i8, ptr @g\n ret i8 %x }',
          '@g=global i8 0, align 1\ndefine i8 @main() { %x=load i8, ptr @g, align 8\n ret i8 %x }',
          '@g=constant i8 0\ndefine i8 @main() { store i8 1, ptr @g\n ret i8 0 }',
          '@g=external global i8\ndefine i8 @main() { ret i8 0 }',
          '@g=global <2 x i8> zeroinitializer\ndefine i8 @main() { ret i8 0 }',
          'define i8 @main() { %x=add i8 0,1, !range !0\nret i8 %x }\n!0=!{i8 0,i8 2}',
          'define void @main() { br label %loop\nloop: br label %loop, !llvm.loop !0 }\n!0=distinct !{!0,!1}\n!1=!{!"llvm.loop.mustprogress"}',
        ]
        for source in cases:
            with self.subTest(source=source): self.candidate(source,ok=False)

    def test_debug_intrinsic_admission(self):
        source=self.path/'debug.c'; source.write_text('int main(void) { int x=3; return x; }')
        path=self.path/'debug.ll'
        subprocess.run([CLANG,'-S','-emit-llvm','-O0','-g','-fno-finite-loops',str(source),'-o',str(path)],check=True,capture_output=True)
        command=[BINARY,'--emit-scalar-bundle','--diagnostics=json',str(path)]
        good=subprocess.run(command,text=True,capture_output=True,timeout=30)
        self.assertEqual(good.returncode,0,good.stderr)
        ir=path.read_text(); lines=ir.splitlines()
        index=next(i for i,line in enumerate(lines) if 'call void @llvm.dbg.declare' in line)
        self.assertIn('), !dbg',lines[index])
        lines[index]=lines[index].replace('), !dbg',') [ "m2.unknown"() ], !dbg')
        path.write_text('\n'.join(lines)+'\n')
        bad=subprocess.run(command,text=True,capture_output=True,timeout=30)
        self.assertEqual(bad.returncode,2,bad.stderr)
        self.assertEqual(bad.stdout,'')

    def test_global_name_collision(self):
        model=self.bundle('''@x=global i8 1, align 1
@x.poison=global i8 2, align 1
define i8 @main() {
 %a=load i8, ptr @x, align 1
 %b=load i8, ptr @x.poison, align 1
 %r=add i8 %a,%b
 ret i8 %r
}''')
        self.assertEqual(self.reach(model,f'{DONE} && {RETURN}=(uint8)3 && !{POISON}',4)['outcome'],'reachable')

    def test_publication_and_deterministic_provenance(self):
        source='define i8 @main() { ret i8 7 }'
        a=self.candidate(source); b=self.candidate(source)
        self.assertEqual(a,b)
        provenance=read_json(a['files']['provenance.json'])
        self.assertEqual(provenance['scope'],'llvm18-scalar-v3')
        self.assertEqual(provenance['origin']['normalization'],'bounded-frames-v1')
        path=self.path/'driver.ll'; path.write_text(HEADER+source)
        destination=self.path/'driver-bundle'
        command=[sys.executable,str(ROOT/'tools/llvm2smv_translate.py'),str(path),'-o',str(destination),
                 '--translator',BINARY,'--checker',CHECKER]
        p=subprocess.run(command,text=True,capture_output=True,timeout=30)
        self.assertEqual(p.returncode,0,p.stderr)
        self.assertIsNone(json.loads(p.stdout)['verification_result'])
        original=(destination/'manifest.json').read_bytes()
        self.assertEqual(subprocess.run(command,capture_output=True,timeout=30).returncode,2)
        self.assertEqual((destination/'manifest.json').read_bytes(),original)
        path.write_text(HEADER+'define i8 @main() { ret i8 undef }')
        self.assertEqual(subprocess.run(command,capture_output=True,timeout=30).returncode,2)
        self.assertEqual((destination/'manifest.json').read_bytes(),original)


if __name__=='__main__': unittest.main()
