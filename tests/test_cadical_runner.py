#!/usr/bin/env python3
"""Fail-closed checks for the opt-in CaDiCaL API runner; no solver needed."""
import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('cadical_runner', ROOT / 'tools/test-cadical-api.py')
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class RunnerTests(unittest.TestCase):
    source = Path('/tmp/cadical source with spaces')

    def invoke(self, *, git=None, files=True, failure=None, options=()):
        replies = git if git is not None else [str(self.source), runner.REVISION, '']
        with patch.object(sys, 'argv', ['test-cadical-api.py', '--source', str(self.source),
                                      '--cxx', 'c++', '--cxxflags=-O2', *options]), \
             patch.object(runner.subprocess, 'check_output', side_effect=replies) as metadata, \
             patch.object(runner.subprocess, 'run', side_effect=failure) as execute, \
             patch.object(Path, 'is_file', autospec=True,
                          side_effect=files if callable(files) else lambda p: files), \
             contextlib.redirect_stdout(io.StringIO()), \
             contextlib.redirect_stderr(io.StringIO()) as errors:
            result = runner.main()
        return result, metadata, execute, errors.getvalue()

    def test_success_uses_argument_lists_and_cleans_temporary_binary(self):
        result, metadata, execute, _ = self.invoke()
        self.assertEqual(result, 0)
        self.assertEqual(metadata.call_count, 3)
        self.assertEqual(execute.call_count, 2)
        compile_call, test_call = execute.call_args_list
        command = compile_call.args[0]
        self.assertIn(str(self.source / 'src'), command)
        self.assertIn(str(self.source / 'build/libcadical.a'), command)
        self.assertNotIn('shell', compile_call.kwargs)
        self.assertEqual(compile_call.kwargs, dict(check=True, timeout=120))
        self.assertEqual(test_call.kwargs, dict(check=True, timeout=60))
        binary = Path(command[-1])
        self.assertEqual(test_call.args[0], [str(binary)])
        self.assertFalse(binary.parent.exists())

    def test_wrong_revision_is_rejected_before_compiling(self):
        result, _, execute, error = self.invoke(git=[str(self.source), '0' * 40])
        self.assertEqual(result, 1)
        execute.assert_not_called()
        self.assertIn('must be pinned', error)

    def test_proof_suite_compiles_reconstruction_and_both_suites_run(self):
        result, _, execute, _ = self.invoke(options=['--suite', 'all'])
        self.assertEqual(result, 0)
        self.assertEqual(execute.call_count, 4)
        command = execute.call_args_list[2].args[0]
        self.assertIn(str(ROOT / 'tests/test_cadical_proof.cc'), command)
        self.assertIn(str(ROOT / 'src/sat/proof.cc'), command)
        self.assertIn(str(ROOT / 'src/sat/circuit.cc'), command)
        self.assertIn(str(ROOT / 'src'), command)

    def test_missing_proof_header_is_rejected(self):
        result, _, execute, error = self.invoke(files=lambda p: p.name != 'tracer.hpp',
                                              options=['--suite', 'proof'])
        self.assertEqual(result, 1)
        execute.assert_not_called()
        self.assertIn('tracer.hpp is missing', error)

    def test_subdirectory_is_not_accepted_as_checkout_root(self):
        result, _, execute, error = self.invoke(git=['/tmp'])
        self.assertEqual(result, 1)
        execute.assert_not_called()
        self.assertIn('checkout root', error)

    def test_dirty_source_is_rejected_before_compiling(self):
        result, _, execute, _ = self.invoke(git=[str(self.source), runner.REVISION,
                                               subprocess.CalledProcessError(1, ['git', 'diff'])])
        self.assertEqual(result, 1)
        execute.assert_not_called()

    def test_missing_library_is_rejected(self):
        result, _, execute, error = self.invoke(files=False)
        self.assertEqual(result, 1)
        execute.assert_not_called()
        self.assertIn('missing', error)

    def test_compile_failure_is_not_reported_as_success(self):
        result, _, execute, _ = self.invoke(failure=subprocess.CalledProcessError(1, ['c++']))
        self.assertEqual(result, 1)
        self.assertEqual(execute.call_count, 1)

    def test_executable_failure_and_timeout_are_not_reported_as_success(self):
        for failure in (subprocess.CalledProcessError(1, ['probe']),
                        subprocess.TimeoutExpired(['probe'], 60)):
            with self.subTest(failure=failure):
                result, _, execute, _ = self.invoke(failure=[None, failure])
                self.assertEqual(result, 1)
                self.assertEqual(execute.call_count, 2)
                self.assertFalse(Path(execute.call_args.args[0][0]).parent.exists())

    def test_invalid_timeouts_are_rejected(self):
        for value in ('0', '-1', 'nan', 'inf'):
            with self.subTest(value=value), self.assertRaises(SystemExit) as error:
                self.invoke(options=['--timeout', value])
            self.assertEqual(error.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
