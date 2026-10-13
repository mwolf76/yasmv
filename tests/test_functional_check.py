#!/usr/bin/env python3
"""Run the shipped checking examples and verify semantic results and replay evidence.

Witness valuations and generated job IDs are intentionally not text snapshots:
solver choices may differ while the same query and evidence remain valid.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    ('cannibals', 'cannibals.smv', 'forward', 'reachable'),
    ('cannibals', 'cannibals.smv', 'backward', 'reachable'),
    ('maze', 'solvable8x8.smv', 'commands', 'reachable'),
    ('maze', 'unsolvable8x8.smv', 'commands', 'unreachable'),
    ('maze', 'solvable12x12.smv', 'commands', 'reachable'),
    ('maze', 'solvable16x16.smv', 'commands', 'reachable'),
    ('vending', 'vending.smv', 'commands', 'reachable'),
    ('herschel', 'herschel.smv', 'commands', 'unreachable'),
    ('koenisberg', 'koenisberg.smv', 'commands', 'unreachable'),
    ('ferryman', 'ferryman.smv', 'commands', 'reachable'),
    ('fifteen', 'fifteen.smv', 'commands', 'reachable'),
    ('hanoi', 'hanoi3.smv', 'commands', 'reachable'),
]


class FunctionalChecks(unittest.TestCase):
    def test_shipped_examples(self):
        for directory, model, commands, expected in CASES:
            with self.subTest(model=model, commands=commands), tempfile.TemporaryDirectory() as temporary:
                folder = ROOT / 'examples' / directory
                store = Path(temporary) / 'workspace'
                script = f'workspace open "{store}"\n' + (folder / commands).read_text()
                result = subprocess.run([os.environ.get('YASMV', str(ROOT / 'yasmv')), '--quiet', str(folder / model)], input=script,
                    text=True, capture_output=True, cwd=temporary,
                    env=dict(os.environ, YASMV_HOME=str(ROOT), XDG_CONFIG_HOME=str(Path(temporary) / 'config')),
                    timeout=float(os.environ.get('YASMV_TEST_TIMEOUT', '60')))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                results = [json.loads(p.read_text()) for p in store.glob('jobs/*/result.json')]
                self.assertEqual(len(results), 1)
                answer = results[0]
                self.assertEqual(answer['status'], 'completed', answer)
                self.assertEqual(answer['outcome'], expected, answer)
                if expected == 'reachable':
                    self.assertTrue(answer['trace_validated'])
                    self.assertIsNotNone(answer['trace'])
                    self.assertEqual(answer['trace']['query']['operation'], 'check')
                    self.assertEqual(answer['trace']['query']['variant'], 'reachable')
                else:
                    self.assertIsNone(answer['trace'])
                    if directory in ('maze', 'koenisberg'):
                        bound = 100 if directory == 'maze' else 8
                        self.assertEqual(answer['scope'], 'through_depth')
                        self.assertEqual(answer['unbounded_outcome'], 'unknown')
                        self.assertEqual(answer['checked_depths'], list(range(bound + 1)))
                    else:
                        self.assertEqual(answer['scope'], 'unbounded')
                        self.assertTrue(answer['proof']['verified'])


if __name__ == '__main__': unittest.main(failfast=True)
