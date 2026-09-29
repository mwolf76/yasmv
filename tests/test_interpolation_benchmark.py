#!/usr/bin/env python3
"""Benchmark accounting, outcome distinctions, and a real four-method smoke run."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('benchmark', ROOT / 'tools/benchmark-interpolation.py')
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


class BenchmarkTests(unittest.TestCase):
    def test_matching_problem_and_explicit_depth_contracts(self):
        case = dict(target='bad', assumptions=['legal'], depth=7)
        for method in benchmark.METHODS:
            query = benchmark.query_for(case, method, 1234)
            self.assertEqual(query['assumptions'], ['legal'])
            self.assertEqual(query['limits']['wall_ms'], 1234)
            if method == 'simple-path':
                self.assertNotIn('depth', query['limits'])
                self.assertEqual(query['target'], 'bad')
            else:
                self.assertEqual(query['limits']['depth'], 7)
                self.assertEqual(query['property']['expression'], '!(bad)')

    def test_outcomes_are_not_upgraded_or_contradicted(self):
        result = dict(status='completed', outcome='holds_bounded', scope='through_depth')
        self.assertEqual(benchmark.summarize(result, 'unsafe')['outcome'], 'holds_bounded')
        with self.assertRaises(ValueError):
            benchmark.summarize(dict(result, outcome='proven', scope='unbounded'), 'unsafe')
        with self.assertRaises(ValueError):
            benchmark.summarize(dict(result, status='unknown', proof={'verified': True}), 'safe')
        with self.assertRaises(ValueError):
            benchmark.summarize(dict(result, outcome='proven', scope='unbounded', proof_method='interpolation'), 'safe')
        self.assertEqual(benchmark.summarize(dict(status='unknown', outcome='none'), 'safe')['status'], 'unknown')

    def test_process_rss_and_hard_timeout(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            larger, _, _ = benchmark.measure([sys.executable, '-c', 'x = bytearray(80 * 1024 * 1024)'], directory, 5)
            measured, stdout, _ = benchmark.measure([sys.executable, '-c', 'print("done")'], directory, 5)
            self.assertEqual(measured['exit_code'], 0)
            self.assertGreater(measured['peak_rss_kib'], 0)
            self.assertGreater(larger['peak_rss_kib'], measured['peak_rss_kib'] + 32768)
            self.assertFalse(measured['hard_timeout'])
            self.assertEqual(stdout.strip(), 'done')
            measured, stdout, _ = benchmark.measure([sys.executable, '-c', 'import time; time.sleep(5)'], directory, .05)
            self.assertTrue(measured['hard_timeout'])
            self.assertGreater(measured['peak_rss_kib'], 0)
            self.assertEqual(stdout, '')

    def test_real_safe_and_unsafe_reports(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'report.json'
            run = subprocess.run([sys.executable, str(ROOT / 'tools/benchmark-interpolation.py'),
                '--case', 'long-cycle-4', '--case', 'arithmetic-unsafe', '--runs', '1', '--output', str(output)],
                capture_output=True, text=True, timeout=180)
            self.assertEqual(run.returncode, 0, run.stderr + run.stdout)
            report = json.loads(output.read_text())
            self.assertTrue(report['complete'])
            self.assertEqual(len(report['cases']), 2)
            for case in report['cases']:
                self.assertEqual(set(case['methods']), set(benchmark.METHODS))
                for method, group in case['methods'].items():
                    sample = group['samples'][0]
                    self.assertFalse(sample['hard_timeout'])
                    self.assertGreater(sample['peak_rss_kib'], 0)
                    self.assertGreater(sample['statistics']['solver_calls'], 0)
                    if case['expected'] == 'unsafe':
                        self.assertIn(sample['outcome'], ('violated', 'reachable'))
                        self.assertEqual(sample['witness_depth'], 1)
                        self.assertEqual(sample['replay']['outcome'], 'valid')
                    elif method == 'interpolation':
                        self.assertEqual(sample['outcome'], 'proven')
                        self.assertTrue(sample['verified'])
                        self.assertGreater(sample['invariant_nodes'], 0)

    def test_native_unknown_exit_code_is_a_sample(self):
        with tempfile.TemporaryDirectory() as temporary:
            measured, result = benchmark.run_query(ROOT / 'yasmv', ROOT / 'tests/models/query.smv', {},
                dict(operation='reach', target='x', limits=dict(wall_ms=0)), Path(temporary), 15, ROOT)
            self.assertEqual(measured['exit_code'], 3)
            self.assertEqual(result['status'], 'unknown')
            self.assertIsNone(result['trace'])
            self.assertEqual(benchmark.summarize(result, 'unsafe')['status'], 'unknown')


if __name__ == '__main__': unittest.main()
