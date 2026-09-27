#!/usr/bin/env python3
"""Typed writer semantics and atomic publication, checked through native yasmv."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import llvm2smv_artifact as bundles

GENERATOR = os.environ.get('LLVM2SMV_MODEL_TESTS', str(ROOT / 'llvm2smv/llvm2smv_model_tests'))
CHECKER = os.environ.get('YASMV', str(ROOT / 'yasmv'))
os.environ.setdefault('YASMV_HOME', str(ROOT))


def symbol(key):
    return 'v_' + key.encode().hex()


def fixture(name):
    return bundles.read_json(subprocess.check_output([GENERATOR, '--fixture', name], text=True, timeout=15))


def rehash(artifact):
    """Construct deliberately invalid but consistently hashed models for validation."""
    files = artifact['files']
    digests = {name: hashlib.sha256(files[name].encode()).hexdigest() for name in sorted(bundles.FILES)}
    identity = 'llvm2smv-model-v1\n' + ''.join(name + '\n' + digest + '\n' for name, digest in digests.items())
    files['manifest.json'] = json.dumps({'version': 1, 'files': digests,
        'artifact_id': hashlib.sha256(identity.encode()).hexdigest()})
    return artifact


class Models(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name)

    def publish(self, name):
        return bundles.publish(fixture(name), self.path / name, CHECKER)

    def query(self, model, query):
        request = self.path / 'query.json'
        request.write_text(json.dumps({'version': 1, 'model': str(model / 'model.smv'), 'query': query}))
        p = subprocess.run([CHECKER, '--quiet', '--query-file', str(request)], text=True,
                           capture_output=True, timeout=30)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        return json.loads(p.stdout)

    def reach(self, model, target, depth):
        return self.query(model, {'operation': 'reach', 'target': target, 'limits': {'depth': depth}})

    def test_sequence_frames_exit_and_properties(self):
        model = self.publish('sequence')
        self.assertEqual(self.reach(model, 'p_646f6e65', 1)['outcome'], 'unreachable')
        r = self.reach(model, 'p_646f6e65', 2)
        self.assertEqual(r['outcome'], 'reachable')
        values = [s['values'] for s in r['trace']['steps']]
        self.assertEqual([(v[symbol('x')], v[symbol('y')]) for v in values], [('0', '0'), ('1', '0'), ('1', '2')])
        self.assertTrue(all(v[symbol('unchanged')] == '7' and v[symbol('immutable')] == '9' for v in values))
        self.assertEqual(self.query(model, {'operation': 'validate-trace', 'trace': r['trace']})['outcome'], 'valid')
        # A false property is observable, never an assumption filtering away states.
        self.assertEqual(self.reach(model, '!p_66616c7365', 0)['outcome'], 'reachable')
        for key, expected in [('unchanged', 7), ('immutable', 9), ('x', 1), ('y', 2)]:
            target = f'p_646f6e65 && {symbol(key)} != (uint8){expected}'
            self.assertEqual(self.reach(model, target, 4)['outcome'], 'unreachable')
        self.assertEqual(self.query(model, {'operation': 'check-trans', 'limits': {'depth': 4}})['outcome'], 'satisfiable')

    def test_simultaneous_rhs(self):
        model = self.publish('swap')
        r = self.reach(model, f'{symbol("x")}=(uint8)2', 1)
        self.assertEqual(r['outcome'], 'reachable')
        self.assertEqual(r['trace']['steps'][1]['values'][symbol('y')], '1')
        self.assertEqual(self.reach(model, f'{symbol("x")}={symbol("y")}', 3)['outcome'], 'unreachable')

    def test_widths_and_exact_constants(self):
        model = self.publish('constants')
        trace = self.query(model, {'operation': 'pick-state'})['trace']
        self.assertEqual(self.query(model, {'operation': 'validate-trace', 'trace': trace})['outcome'], 'valid')
        values = trace['steps'][0]['values']
        for width in (1, 8, 16, 32, 64):
            self.assertEqual(values[symbol('u' + str(width))], str((1 << width) - 1))
            self.assertEqual(values[symbol('s' + str(width))], str(-(1 << (width - 1))))
        for key, expected in [('boolean', True), ('truncated', '0'), ('signed_extension', '65535'), ('zero_extension', '255')]:
            self.assertEqual(values[symbol(key)], expected)

    def test_typed_operators(self):
        model = self.publish('operators')
        trace = self.query(model, {'operation': 'pick-state'})['trace']
        values = trace['steps'][0]['values']
        expected = dict(add='7', sub='3', mul='10', div='2', rem='1',
                        shl='20', shr='1', eq=False, ne=True, lt=False, le=False,
                        gt=True, ge=True, neg='251', select='5', signed_less=True,
                        unsigned_less=False, bool_and=False, bool_or=True,
                        bool_xor=True, bool_not=False)
        expected.update({'and': '0', 'or': '7', 'xor': '7', 'not': '250'})
        for key, value in expected.items():
            self.assertEqual(values[symbol(key)], value, key)
        self.assertEqual(self.query(model, {'operation': 'validate-trace', 'trace': trace})['outcome'], 'valid')

    def test_array_updates_and_frames(self):
        model = self.publish('arrays')
        r = self.reach(model, f'{symbol("a")}[0]=(uint8)2', 1)
        self.assertEqual(r['outcome'], 'reachable')
        values = [s['values'] for s in r['trace']['steps']]
        self.assertEqual([v[symbol('a')] for v in values], [['1', '2'], ['2', '1']])
        self.assertEqual([v[symbol('b')] for v in values], [[True, False], [True, False]])
        self.assertEqual(self.query(model, {'operation': 'validate-trace', 'trace': r['trace']})['outcome'], 'valid')

    def test_choice_is_fresh(self):
        model = self.publish('choice')
        # Requires different values of choice at steps 0 and 1. A frozen choice fails.
        r = self.reach(model, f'{symbol("a_state")} && !{symbol("z_choice")}', 1)
        self.assertEqual(r['outcome'], 'reachable')
        self.assertEqual([s['values'][symbol('z_choice')] for s in r['trace']['steps']], [True, False])
        self.assertNotIn('#input', (model / 'model.smv').read_text())

    def test_identifiers(self):
        model = self.publish('names')
        values = self.query(model, {'operation': 'pick-state'})['trace']['steps'][0]['values']
        self.assertEqual(len(values), 5)
        self.assertTrue(all(v is True for v in values.values()))

    def test_deterministic_artifact_and_publication(self):
        a = fixture('sequence')
        self.assertEqual(a, fixture('sequence-reverse'))
        self.assertEqual(a, fixture('sequence'))
        one = bundles.publish(a, self.path / 'one', CHECKER)
        two = bundles.publish(a, self.path / 'two', CHECKER)
        self.assertEqual(set(p.name for p in one.iterdir()), bundles.FILES | {'manifest.json'})
        for name, content in a['files'].items():
            self.assertEqual((one / name).read_text(), content)
            self.assertEqual((two / name).read_text(), content)
        changed = copy.deepcopy(a)
        provenance = json.loads(changed['files']['provenance.json'])
        provenance['origin']['producer'] = 'different source'
        changed['files']['provenance.json'] = json.dumps(provenance)
        changed = rehash(changed)
        self.assertNotEqual(json.loads(a['files']['manifest.json'])['artifact_id'],
                            json.loads(changed['files']['manifest.json'])['artifact_id'])

    def test_existing_destinations_preserved(self):
        a = fixture('swap')
        (self.path / 'file').write_text('original')
        (self.path / 'dir').mkdir()
        (self.path / 'link').symlink_to(self.path / 'missing')
        for name in ('file', 'dir', 'link'):
            with self.assertRaises(FileExistsError):
                bundles.publish(a, self.path / name, CHECKER)
        self.assertEqual((self.path / 'file').read_text(), 'original')
        self.assertFalse(list((self.path / 'dir').iterdir()))
        self.assertTrue((self.path / 'link').is_symlink())
        self.assertEqual(sorted(p.name for p in self.path.iterdir()), ['dir', 'file', 'link'])

    def test_validation_rejects_bad_models(self):
        for name, model in [('overlap', None), ('bad-type', 'MODULE main\nVAR x:boolean;\nINIT x + TRUE;\n'),
                            ('bad-syntax', 'this is not SMV')]:
            with self.subTest(name=name):
                a = fixture('overlap' if model is None else 'swap')
                if model is not None:
                    a['files']['model.smv'] = model
                    rehash(a)
                with self.assertRaises(bundles.ArtifactError):
                    bundles.publish(a, self.path / name, CHECKER)
                self.assertFalse(list(self.path.iterdir()))

    def test_reject_tampering_and_envelopes(self):
        a = fixture('swap')
        bad = []
        for filename in a['files']:
            b = copy.deepcopy(a); b['files'][filename] += 'x'; bad.append(b)
        b = copy.deepcopy(a); b['files']['../escape'] = 'x'; bad.append(b)
        b = copy.deepcopy(a); b['version'] = True; bad.append(b)
        b = copy.deepcopy(a); del b['files']['properties.json']; bad.append(b)
        for b in bad:
            with self.assertRaises(ValueError):
                bundles.publish(b, self.path / 'output', CHECKER)
        with self.assertRaises(bundles.ArtifactError):
            bundles.read_json('{"version":1,"version":1}')
        self.assertFalse(list(self.path.iterdir()))

    def test_checker_failure_and_timeout_cleanup(self):
        checker = self.path / 'checker'
        for body in ["print('garbage')", "print('{\"version\":1,\"status\":\"unknown\",\"outcome\":null}')",
                     "print('{\"version\":true,\"status\":\"completed\",\"outcome\":\"valid\"}')",
                     "raise SystemExit(2)", 'import time; time.sleep(10)']:
            with self.subTest(body=body):
                checker.write_text('#!' + sys.executable + '\n' + body + '\n'); checker.chmod(0o755)
                with self.assertRaises(bundles.ArtifactError):
                    bundles.publish(fixture('swap'), self.path / 'out', checker, timeout=0.2)
                self.assertEqual([p.name for p in self.path.iterdir()], ['checker'])

    def test_publication_race_never_overwrites(self):
        rename = bundles._rename_new
        for kind in ('empty-directory', 'directory', 'file', 'symlink'):
            dest = self.path / kind
            def racing_rename(source, destination):
                if kind == 'file':
                    dest.write_text('winner')
                elif kind == 'symlink':
                    dest.symlink_to(self.path / 'missing')
                else:
                    dest.mkdir()
                    if kind == 'directory':
                        (dest / 'sentinel').write_text('winner')
                rename(source, destination)
            with self.subTest(kind=kind), patch.object(bundles, '_rename_new', side_effect=racing_rename):
                with self.assertRaises(FileExistsError):
                    bundles.publish(fixture('swap'), dest, CHECKER)
            if kind == 'empty-directory':
                self.assertEqual(list(dest.iterdir()), [])
            elif kind == 'directory':
                self.assertEqual((dest / 'sentinel').read_text(), 'winner')
            elif kind == 'file':
                self.assertEqual(dest.read_text(), 'winner')
            else:
                self.assertTrue(dest.is_symlink())
        self.assertEqual(sorted(p.name for p in self.path.iterdir()),
                         ['directory', 'empty-directory', 'file', 'symlink'])

    def test_timeout_contract(self):
        for timeout in (0, -1, float('inf'), float('nan'), True, '30'):
            with self.assertRaises(bundles.ArtifactError):
                bundles.publish(fixture('swap'), self.path / 'out', CHECKER, timeout=timeout)
        self.assertFalse(list(self.path.iterdir()))


if __name__ == '__main__':
    unittest.main()
