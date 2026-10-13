#!/usr/bin/env python3
"""Check bootstrap defaults and failure handling without invoking a toolchain."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
REVISION = 'c60730422e758ef1cebe7aeddf2dda31c996bf04'


class SetupTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='yasmv-setup-test-')
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        shutil.copyfile(ROOT / 'setup.sh', self.directory / 'setup.sh')
        (self.directory / 'bin').mkdir()
        (self.directory / 'microcode').mkdir()
        self.marker = self.directory / 'microcode/u-ge-26.json'
        self.marker.touch()
        for command in ('dirname', 'mkdir', 'mktemp', 'mv', 'rmdir', 'rm', 'install', 'cat', 'cp'):
            (self.directory / 'bin' / command).symlink_to(shutil.which(command))
        for command, body in {
            'bin/tar': 'echo tar >> "$TEST_ROOT/calls"\nexit "${TAR_STATUS:-0}"\n',
            'bin/autoreconf': 'echo autoreconf >> "$TEST_ROOT/calls"\nexit "${AUTORECONF_STATUS:-0}"\n',
            'bin/gcc': 'echo "mock compiler ${COMPILER_VERSION:-1}"\n',
            'bin/g++': 'echo "mock compiler ${COMPILER_VERSION:-1}"\n',
            'bin/git': '''case $1 in
clone)
    echo clone >> "$TEST_ROOT/calls"
    [ "${CLONE_STATUS:-0}" = 0 ] || exit "$CLONE_STATUS"
    for argument do destination=$argument; done
    mkdir -p "$destination/src"
    cp "$TEST_ROOT/upstream-configure" "$destination/configure"
    echo header > "$destination/src/cadical.hpp"
    echo tracer > "$destination/src/tracer.hpp"
    ;;
-C)
    case $3 in
        rev-parse) echo "${SOURCE_REVISION:-''' + REVISION + '''}" ;;
        diff) exit "${SOURCE_DIRTY:-0}" ;;
        *) exit 2 ;;
    esac
    ;;
*) exit 2 ;;
esac
''',
            'upstream-configure': '''echo cadical-configure >> "$TEST_ROOT/calls"
for argument do printf '%s\\n' "$argument"; done > "$TEST_ROOT/cadical-arguments"
printf '%s' "$CFLAGS$CXXFLAGS" > "$TEST_ROOT/cadical-flags"
[ "${CADICAL_CONFIGURE_STATUS:-0}" = 0 ] || exit "$CADICAL_CONFIGURE_STATUS"
mkdir -p build
''',
            'bin/make': '''make_directory=
previous=
for argument do
    [ "$previous" != -C ] || make_directory=$argument
    previous=$argument
done
if [ "$previous" = libcadical.a ]; then
    echo cadical-make >> "$TEST_ROOT/calls"
    for argument do printf '%s\\n' "$argument"; done > "$TEST_ROOT/cadical-make-arguments"
    [ "${CADICAL_MAKE_STATUS:-0}" = 0 ] || exit "$CADICAL_MAKE_STATUS"
    echo archive > "$make_directory/libcadical.a"
else
    echo make >> "$TEST_ROOT/calls"
    for argument do printf '%s\\n' "$argument"; done > "$TEST_ROOT/make-arguments"
    exit "${MAKE_STATUS:-0}"
fi
''',
            'configure': 'echo configure >> calls\nprintf "%s\\n" "$@" > arguments\n'
                         'exit "${CONFIGURE_STATUS:-0}"\n',
        }.items():
            script = self.directory / command
            script.write_text('#!/bin/sh\n' + body)
            script.chmod(0o755)

    def run_setup(self, *arguments, bootstrap=False, cwd=None, **environment):
        if not bootstrap:
            environment.setdefault('CADICAL_PREFIX', '/external')
        return subprocess.run(
            ['/bin/sh', str(self.directory / 'setup.sh'), *arguments],
            cwd=cwd or self.directory,
            env=dict(PATH=str(self.directory / 'bin'), TEST_ROOT=str(self.directory),
                     **environment),
            capture_output=True, text=True, timeout=10)

    def calls(self):
        return (self.directory / 'calls').read_text().splitlines()

    def arguments(self):
        return (self.directory / 'arguments').read_text().splitlines()

    def test_external_prefix_preserves_release_linked_llvm_settings(self):
        result = self.run_setup()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ['autoreconf', 'configure', 'make'])
        self.assertEqual(self.arguments(), [
            '--prefix=/usr/local', '--enable-llvm2smv',
            '--with-cadical-prefix=/external', 'CC=gcc', 'CXX=g++', 'CFLAGS=-O2',
            'CXXFLAGS=-D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -DPIC '
            '-fPIC -std=c++20 -O2 -Wall -Wno-deprecated-declarations -Werror',
        ])

    def test_environment_prefix_and_explicit_overrides(self):
        overrides = ['--disable-llvm2smv', '--with-cadical-prefix=/explicit',
                     '--prefix=/opt/yasmv', 'CXX=clang++', 'CXXFLAGS=-std=c++20 -O1']
        result = self.run_setup(*overrides, CADICAL_PREFIX='/environment')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ['autoreconf', 'configure', 'make'])
        self.assertEqual(self.arguments()[2], '--with-cadical-prefix=/explicit')
        self.assertEqual(self.arguments()[-len(overrides):], overrides)

    def test_missing_microcode_is_extracted_before_configuration(self):
        self.marker.unlink()
        result = self.run_setup()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ['tar', 'autoreconf', 'configure', 'make'])

    def test_extraction_failure_stops_setup(self):
        self.marker.unlink()
        result = self.run_setup(TAR_STATUS='7')
        self.assertEqual(result.returncode, 7)
        self.assertEqual(self.calls(), ['tar'])
        self.assertNotIn('done.', result.stdout)

    def test_autoreconf_failure_stops_setup(self):
        result = self.run_setup(AUTORECONF_STATUS='8')
        self.assertEqual(result.returncode, 8)
        self.assertEqual(self.calls(), ['autoreconf'])

    def test_configure_failure_is_propagated(self):
        result = self.run_setup(CONFIGURE_STATUS='9')
        self.assertEqual(result.returncode, 9)
        self.assertEqual(self.calls(), ['autoreconf', 'configure'])

    def test_build_uses_nproc(self):
        script = self.directory / 'bin/nproc'
        script.write_text('#!/bin/sh\necho 8\n')
        script.chmod(0o755)
        result = self.run_setup()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.directory / 'make-arguments').read_text().splitlines(),
                         ['-j', '8'])

    def test_build_without_nproc_uses_plain_make(self):
        result = self.run_setup()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.directory / 'make-arguments').read_text(), '')

    def test_failed_nproc_falls_back_to_plain_make(self):
        script = self.directory / 'bin/nproc'
        script.write_text('#!/bin/sh\nexit 1\n')
        script.chmod(0o755)
        result = self.run_setup()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.directory / 'make-arguments').read_text(), '')

    def test_build_failure_is_propagated(self):
        result = self.run_setup(MAKE_STATUS='10')
        self.assertEqual(result.returncode, 10)
        self.assertEqual(self.calls(), ['autoreconf', 'configure', 'make'])

    def test_no_arguments_bootstraps_pinned_release_and_reuses_it(self):
        source = self.directory / '.deps' / ('cadical-' + REVISION)
        prefix = source / 'prefix'
        result = self.run_setup(bootstrap=True, CXXFLAGS='-O0 -g', CFLAGS='-O0')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ['clone', 'cadical-configure', 'cadical-make',
                                       'autoreconf', 'configure', 'make'])
        self.assertEqual((self.directory / 'cadical-arguments').read_text(), '-fPIC\n')
        self.assertEqual((self.directory / 'cadical-flags').read_text(), '')
        self.assertIn('--with-cadical-prefix=' + str(prefix), self.arguments())
        self.assertTrue((prefix / 'lib/libcadical.a').is_file())
        self.assertTrue((prefix / 'include/cadical.hpp').is_file())
        self.assertEqual((prefix / 'include/tracer.hpp').read_text(), 'tracer\n')
        self.assertTrue((prefix / '.yasmv-build-config').is_file())
        result = self.run_setup(bootstrap=True, CLONE_STATUS='99')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls().count('clone'), 1)
        self.assertEqual(self.calls().count('cadical-make'), 1)
        self.assertIn('cached', result.stdout)

    def test_bootstrap_uses_nproc_for_dependency_and_project(self):
        script = self.directory / 'bin/nproc'
        script.write_text('#!/bin/sh\necho 8\n')
        script.chmod(0o755)
        result = self.run_setup(bootstrap=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        for filename in ('cadical-make-arguments', 'make-arguments'):
            self.assertEqual((self.directory / filename).read_text().splitlines()[:2],
                             ['-j', '8'])

    def test_failed_download_can_be_retried(self):
        result = self.run_setup(bootstrap=True, CLONE_STATUS='11')
        self.assertEqual(result.returncode, 11)
        self.assertEqual(self.calls(), ['clone'])
        result = self.run_setup(bootstrap=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_wrong_revision_and_modified_source_stop_bootstrap(self):
        result = self.run_setup(bootstrap=True, SOURCE_REVISION='wrong')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.calls(), ['clone'])
        self.assertIn('unmodified pinned revision', result.stderr)
        result = self.run_setup(bootstrap=True, SOURCE_DIRTY='1')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.calls(), ['clone'])

    def test_failed_dependency_build_is_not_cached(self):
        result = self.run_setup(bootstrap=True, CADICAL_MAKE_STATUS='12')
        self.assertEqual(result.returncode, 12)
        self.assertNotIn('configure', self.calls())
        prefix = self.directory / '.deps' / ('cadical-' + REVISION) / 'prefix'
        self.assertFalse((prefix / '.yasmv-build-config').exists())
        result = self.run_setup(bootstrap=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls().count('cadical-make'), 2)

    def test_compiler_change_rebuilds_dependency(self):
        self.assertEqual(self.run_setup(bootstrap=True).returncode, 0)
        result = self.run_setup(bootstrap=True, COMPILER_VERSION='2')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls().count('clone'), 1)
        self.assertEqual(self.calls().count('cadical-make'), 2)

    def test_missing_proof_header_repairs_cached_prefix(self):
        self.assertEqual(self.run_setup(bootstrap=True).returncode, 0)
        header = self.directory / '.deps' / ('cadical-' + REVISION) / 'prefix/include/tracer.hpp'
        header.unlink()
        result = self.run_setup(bootstrap=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(header.read_text(), 'tracer\n')
        self.assertEqual(self.calls().count('clone'), 1)
        self.assertEqual(self.calls().count('cadical-make'), 2)

    def test_failed_rebuild_invalidates_existing_cache_marker(self):
        self.assertEqual(self.run_setup(bootstrap=True).returncode, 0)
        result = self.run_setup(bootstrap=True, COMPILER_VERSION='2',
                                CADICAL_MAKE_STATUS='12')
        self.assertEqual(result.returncode, 12)
        marker = self.directory / '.deps' / ('cadical-' + REVISION) / 'prefix/.yasmv-build-config'
        self.assertFalse(marker.exists())
        self.assertEqual(self.run_setup(bootstrap=True).returncode, 0)
        self.assertEqual(self.calls().count('cadical-make'), 3)

    def test_explicit_prefix_skips_download_without_environment(self):
        for arguments in (['--with-cadical-prefix=/explicit'],
                          ['--with-cadical-prefix', '/explicit']):
            with self.subTest(arguments=arguments):
                result = self.run_setup(*arguments, bootstrap=True, CLONE_STATUS='99')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertNotIn('clone', self.calls())
                self.assertEqual(self.arguments()[2], '--with-cadical-prefix=/explicit')

    def test_invocation_outside_checkout(self):
        result = self.run_setup(cwd=self.directory / 'bin')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ['autoreconf', 'configure', 'make'])


if __name__ == '__main__':
    unittest.main()
