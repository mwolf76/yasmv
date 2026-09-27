#!/usr/bin/env python3
"""M0 rejection, feature inventory, toolchain, and artifact-preservation contracts."""
import json
import os
import shlex
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/llvm2smv'
BINARY = Path(os.environ.get('LLVM2SMV', ROOT / 'llvm2smv/llvm2smv')).resolve()
CLANG = os.environ.get('CLANG', 'clang-18')
OPT = os.environ.get('LLVM_OPT', 'opt-18')
LINK = os.environ.get('LLVM_LINK', 'llvm-link-18')


class TranslatorTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='llvm2smv-test-')
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name)

    def run_tool(self, *arguments, expected=2):
        result = subprocess.run([str(BINARY), *map(str, arguments)], text=True,
                                capture_output=True, timeout=15)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def analyze(self, source='minimal.ll', *options):
        path = FIXTURES / source if isinstance(source, str) else source
        result = self.run_tool('--analyze', *options, path)
        self.assertEqual(result.stderr, '')
        report = json.loads(result.stdout)
        self.assertEqual(report['version'], 1)
        self.assertFalse(report['translation_available'])
        return report

    def fixture(self, text):
        path = self.path / 'input.ll'
        path.write_text(text)
        return path

    def test_capabilities_never_claim_translation_support(self):
        result = self.run_tool('--capabilities', expected=0)
        report = json.loads(result.stdout)
        self.assertEqual(report['required_llvm_major'], 18)
        self.assertEqual(report['milestone'], 'M4')
        self.assertTrue(report['scalar_candidate_available'])
        self.assertTrue(report['typed_model_foundation'])
        self.assertEqual(report['supported_features'], [])
        self.assertFalse(report['translation_available'])
        self.assertEqual(result.stderr, '')

    def test_minimal_inventory_and_default_rejection(self):
        report = self.analyze()
        self.assertEqual(report['status'], 'unsupported')
        self.assertEqual(report['inventory']['opcodes'], {'ret': 1})
        self.assertEqual(report['inventory']['functions'][0]['name'], 'main')
        self.assertIn('i32', report['inventory']['types'])
        result = self.run_tool(FIXTURES / 'minimal.ll')
        self.assertEqual(result.stdout, '')
        self.assertIn('[unsupported-instruction]', result.stderr)
        self.assertIn('ret i32 0', result.stderr)
        self.assertIn('[translation-unavailable]', result.stderr)
        self.assertIn('(type i32)', result.stderr)

    def test_rejection_preserves_existing_missing_and_symlink_destinations(self):
        target = self.path / 'destination.smv'
        sentinel = b'previous model\n'
        target.write_bytes(sentinel)
        link = self.path / 'link.smv'
        link.symlink_to(target)
        missing = self.path / 'missing.smv'
        for output in (target, link, missing, self.path / 'missing-dir' / 'out.smv'):
            with self.subTest(output=output):
                result = self.run_tool(FIXTURES / 'features.ll', '-o', output, '--diagnostics=json')
                self.assertEqual(result.stdout, '')
                self.assertEqual(json.loads(result.stderr)['status'], 'unsupported')
                self.assertEqual(target.read_bytes(), sentinel)
                self.assertTrue(link.is_symlink())
                self.assertFalse(missing.exists())
        self.assertEqual(self.run_tool(FIXTURES / 'minimal.ll', '-o', '-').stdout, '')

    def test_complete_direct_call_closure_and_attributes(self):
        report = self.analyze('features.ll')
        inv = report['inventory']
        self.assertEqual([f['name'] for f in inv['functions']], ['main', 'helper', 'external'])
        helper = inv['functions'][1]
        self.assertTrue(any(a['attribute'] == 'mustprogress' for a in helper['attributes']))
        self.assertTrue(any(a['attribute'] == 'willreturn' for a in helper['attributes']))
        self.assertIn('i65', inv['types'])
        self.assertEqual(inv['opcodes']['freeze'], 1)
        self.assertEqual(inv['opcodes']['call'], 2)
        call = next(i for i in inv['functions'][0]['instructions'] if i['opcode'] == 'call')
        self.assertEqual(call['operand_bundle_count'], 1)
        self.assertEqual(call['callee'], 'helper')
        self.assertTrue(all(not i['supported'] for f in inv['functions'] for i in f['instructions']))
        self.assertIn('nsw', helper['instructions'][0]['ir'])
        self.assertIn('poison', helper['instructions'][1]['ir'])
        self.assertIn('exact', helper['instructions'][2]['ir'])
        self.assertIn('volatile', helper['instructions'][3]['ir'])
        self.assertIn(r'\03\07', inv['globals'][0]['ir'])
        self.assertEqual(len(inv['aliases']), 1)
        codes = {d['code'] for d in report['diagnostics']}
        self.assertTrue({'unsupported-alias', 'unsupported-global', 'unsupported-attributes',
                         'unsupported-external-call'} <= codes)
        text = self.run_tool(FIXTURES / 'features.ll').stderr
        self.assertIn('(global data)', text)
        self.assertIn('attribute: mustprogress', text)

    def test_missing_and_declared_entry_never_fall_back(self):
        for body in ('define i32 @other() { ret i32 0 }',
                     'declare i32 @main()\ndefine i32 @other() { ret i32 0 }'):
            report = self.analyze(self.fixture(body))
            self.assertIn('invalid-entry', {d['code'] for d in report['diagnostics']})
            self.assertEqual(report['inventory']['functions'], [])
        report = self.analyze(self.fixture('define i32 @other() { ret i32 0 }'), '--entry=other')
        self.assertEqual(report['inventory']['functions'][0]['name'], 'other')

    def test_missing_layout_is_not_filled_from_host(self):
        report = self.analyze(self.fixture('define void @main() { ret void }'))
        codes = {d['code'] for d in report['diagnostics']}
        self.assertTrue({'missing-target', 'missing-data-layout'} <= codes)
        self.assertEqual(report['data_layout'], '')
        self.assertEqual(report['target_triple'], '')

    def test_parse_and_verifier_failures(self):
        for body in ('this is not LLVM IR', 'define i32 @main() { %x = add i32 %x, 1\nret i32 %x }'):
            path = self.fixture(body)
            report = self.analyze(path)
            self.assertEqual(report['status'], 'error')
            self.assertEqual(report['diagnostics'][0]['code'], 'invalid-ir')
            target = self.path / 'out.smv'
            target.write_text('preserve')
            result = self.run_tool(path, '-o', target, '--diagnostics=json')
            self.assertEqual(result.stdout, '')
            self.assertEqual(json.loads(result.stderr)['status'], 'error')
            self.assertEqual(target.read_text(), 'preserve')

    def test_recursive_and_indirect_calls_are_not_silently_dropped(self):
        report = self.analyze(self.fixture('''
define void @main(ptr %f) {
  call void @main(ptr %f)
  call void %f()
  ret void
}
'''))
        functions = report['inventory']['functions']
        self.assertEqual(len(functions), 1)
        self.assertEqual(functions[0]['instructions'][0]['callee'], 'main')
        self.assertIsNone(functions[0]['instructions'][1]['callee'])
        self.assertEqual(report['inventory']['opcodes']['call'], 2)

    def test_unsupported_type_and_instruction_families(self):
        bodies = [
            'define double @main(double %x) { %r = fadd double %x, 1.0\nret double %r }',
            'define <2 x i8> @main(<2 x i8> %x) { %r = add <2 x i8> %x, %x\nret <2 x i8> %r }',
            'define i32 @main(ptr %p) { %r = atomicrmw add ptr %p, i32 1 seq_cst\nret i32 %r }',
            'define void @main() { call void asm sideeffect "", ""()\nret void }',
            'define i32 @main() { %x = alloca i32\nstore i32 3, ptr %x\n%r = load i32, ptr %x\nret i32 %r }',
        ]
        for body in bodies:
            with self.subTest(body=body):
                path = self.fixture(body)
                report = self.analyze(path)
                self.assertEqual(report['status'], 'unsupported')
                instructions = report['inventory']['functions'][0]['instructions']
                rejected = [d for d in report['diagnostics'] if d['code'] == 'unsupported-instruction']
                self.assertEqual(len(rejected), len(instructions))
                self.assertEqual(self.run_tool(path).stdout, '')

    def test_reports_are_deterministic(self):
        first = self.run_tool('--analyze', FIXTURES / 'features.ll')
        second = self.run_tool('--analyze', FIXTURES / 'features.ll')
        self.assertEqual(first.stdout, second.stdout)

    def test_invalid_options_and_missing_input(self):
        for arguments in ([], ['--entry='], ['--capabilities', str(FIXTURES / 'minimal.ll')],
                          ['--analyze', str(FIXTURES / 'minimal.ll'), '-o', str(self.path / 'out.smv')]):
            result = self.run_tool('--diagnostics=json', *arguments)
            report = json.loads(result.stdout or result.stderr)
            self.assertEqual(report['status'], 'error')
        self.assertFalse((self.path / 'out.smv').exists())
        self.run_tool('--word-width=8', FIXTURES / 'minimal.ll', expected=1)

    def test_clang_counter_debug_locations_bitcode_and_matched_tools(self):
        version = json.loads(self.run_tool('--capabilities', expected=0).stdout)['llvm_version']
        for tool in (CLANG, OPT, LINK):
            output = subprocess.run([tool, '--version'], check=True, capture_output=True, text=True).stdout
            self.assertIn('version ' + version, output)
        source = ROOT / 'llvm2smv/examples/simple/counter.c'
        ir = self.path / 'counter.ll'
        subprocess.run([CLANG, '-O0', '-g', '-S', '-emit-llvm', str(source), '-o', str(ir)], check=True)
        report = self.analyze(ir)
        self.assertEqual(report, self.analyze(ir))
        self.assertIn('br', report['inventory']['opcodes'])
        self.assertIn('load', report['inventory']['opcodes'])
        self.assertTrue(any(d['source'] and d['source']['file'].endswith('counter.c')
                            for d in report['diagnostics']))
        bitcode = self.path / 'counter.bc'
        subprocess.run([OPT, '-passes=verify', str(ir), '-o', str(bitcode)], check=True)
        linked = self.path / 'linked.bc'
        subprocess.run([LINK, str(bitcode), '-o', str(linked)], check=True)
        binary_report = self.analyze(linked)
        self.assertEqual(binary_report['inventory']['opcodes'], report['inventory']['opcodes'])
        self.assertEqual(binary_report['target_triple'], report['target_triple'])
        result = self.run_tool(ir)
        self.assertEqual(result.stdout, '')
        self.assertIn('counter.c:', result.stderr)

    def test_compile_script_propagates_failure_and_handles_spaces(self):
        script = ROOT / 'llvm2smv/examples/simple/compile.sh'
        source = self.path / 'source with spaces.c'
        output = self.path / 'result with spaces.ll'
        env = dict(os.environ, CLANG=CLANG)
        source.write_text('int main(void) { return 0; }')
        subprocess.run([str(script), str(source), str(output)], env=env, check=True, capture_output=True)
        self.assertTrue(output.exists())
        source.write_text('invalid C syntax!')
        result = subprocess.run([str(script), str(source), str(output)], env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn('Generated', result.stdout)


class ConfigureTests(unittest.TestCase):
    """Exercise the real AC_LLVM macro in a minimal generated configure script."""
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='llvm2smv-configure-')
        cls.addClassCleanup(cls.directory.cleanup)
        cls.root = Path(cls.directory.name)
        macro = (ROOT / 'm4/llvm.m4').read_text()
        (cls.root / 'configure.ac').write_text(
            'AC_INIT([llvm2smv-contract], [1])\n'
            'm4_define([AM_CONDITIONAL], [])\n' + macro +
            '\nAC_LLVM\nAC_CONFIG_FILES([result])\nAC_OUTPUT\n')
        (cls.root / 'result.in').write_text(
            'config=@LLVM_CONFIG@\nclang=@CLANG@\nopt=@LLVM_OPT@\nlink=@LLVM_LINK@\nlibs=@LLVM_LIBS@\n')
        subprocess.run(['autoconf'], cwd=cls.root, check=True, capture_output=True)

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='llvm2smv-config-case-')
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name)
        self.bin = self.path / 'tools with spaces'
        self.bin.mkdir()
        self.log = self.path / 'calls'
        self.config = self.bin / 'llvm-config-18'
        self.config_version = '18.1.3'
        self.write_config()
        for tool in ('clang', 'opt', 'llvm-link'):
            self.script(self.bin / tool, 'echo "tool version 18.1.3"\n')

    @staticmethod
    def script(path, body):
        path.write_text('#!/bin/sh\n' + body)
        path.chmod(0o755)

    def write_config(self):
        self.script(self.config,
            'printf "%s\\n" "$*" >> ' + shlex.quote(str(self.log)) + '\n'
            'case "$1" in\n'
            '--version) echo ' + shlex.quote(self.config_version) + ';;\n'
            '--bindir) echo ' + shlex.quote(str(self.bin)) + ';;\n'
            '--cppflags) echo "-DTEST_LLVM";;\n'
            '--ldflags) echo "";;\n'
            '--libs) echo "-lLLVM-18 -lz";;\n'
            '*) exit 9;;\nesac\n')

    def configure(self, *options, expected=0, **overrides):
        env = dict(os.environ)
        for name in ('LLVM_CONFIG', 'CLANG', 'LLVM_OPT', 'LLVM_LINK'):
            env.pop(name, None)
        env.update(overrides)
        env['PATH'] = str(self.bin) + os.pathsep + env['PATH']
        result = subprocess.run([str(self.root / 'configure'), *options],
                                cwd=self.path, env=env, capture_output=True, text=True, timeout=20)
        if expected == 0:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def test_versioned_discovery_and_matched_installation(self):
        self.configure()
        result = (self.path / 'result').read_text()
        self.assertIn('config=' + str(self.config), result)
        for tool in ('clang', 'opt', 'llvm-link'):
            self.assertIn(str(self.bin / tool), result)
        self.assertIn('--libs core irreader support analysis transformutils targetparser --system-libs', self.log.read_text())

    def test_core_only_never_invokes_llvm(self):
        self.script(self.config, 'echo invoked > ' + shlex.quote(str(self.log)) + '\nexit 99\n')
        self.configure('--disable-llvm2smv', '--with-llvm-config=' + str(self.config),
                       CLANG=str(self.config), LLVM_OPT=str(self.config), LLVM_LINK=str(self.config))
        self.assertFalse(self.log.exists())
        self.assertIn('clang=no', (self.path / 'result').read_text())

    def test_wrong_llvm_major_is_rejected(self):
        self.config_version = '19.1.0'
        self.write_config()
        result = self.configure('--with-llvm-config=' + str(self.config), expected=1)
        self.assertIn('requires LLVM 18', result.stderr)

    def test_mismatched_override_is_rejected(self):
        wrong = self.path / 'clang'
        self.script(wrong, 'echo "clang version 18.1.8"\n')
        result = self.configure(CLANG=str(wrong), expected=1)
        self.assertIn('must match LLVM 18.1.3', result.stderr)

    def test_missing_tool_is_rejected(self):
        (self.bin / 'llvm-link').unlink()
        result = self.configure(expected=1)
        self.assertIn('cannot execute', result.stderr)

    def test_disabled_option_is_validated(self):
        result = self.configure('--enable-llvm2smv=maybe', expected=1)
        self.assertIn('expects yes or no', result.stderr)


if __name__ == '__main__':
    unittest.main()
