#!/usr/bin/env python3
"""Process-level correctness regressions; run from any working directory."""
import itertools
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ENV = dict(os.environ, YASMV_HOME=str(ROOT))
BINARY = Path(os.environ.get("YASMV", str(ROOT / "yasmv"))).resolve()


class CheckerTests(unittest.TestCase):
    def run_model(self, model, commands="check-init\nquit\n", options=(), code=0):
        with tempfile.TemporaryDirectory(prefix="yasmv-test-") as directory:
            path = Path(directory) / "model.smv"
            path.write_text(model)
            result = subprocess.run([str(BINARY), "--quiet", *options, str(path)],
                                    input=commands, text=True, capture_output=True,
                                    env=ENV, cwd=ROOT, timeout=20)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        return result

    def test_contradiction_with_supported_cnf_options(self):
        for toggles in itertools.product(("yes", "no"), repeat=3):
            options = tuple(itertools.chain.from_iterable(zip(
                ("--cnf-tautology-removal", "--cnf-duplicate-removal", "--cnf-subsumption"), toggles)))
            with self.subTest(options=options):
                r = self.run_model("MODULE main\nVAR x : boolean;\nINIT x && !x;\n", options=options)
                self.assertIn("consistency check failed", r.stdout)

    def test_quarantined_options(self):
        for option in ("blocked-clause", "variable-elimination", "self-subsumption"):
            for value in ("yes", "true", "1", "on"):
                with self.subTest(option=option, value=value):
                    r = self.run_model("MODULE main;", options=("--cnf-" + option, value), code=2)
                    self.assertIn("Unsupported option", r.stderr)
                    self.assertNotIn("consistency check ok", r.stdout)

    def test_relational_crash_original(self):
        r = self.run_model((ROOT / "short-tests/relational/relational01.smv").read_text())
        self.assertIn("consistency check failed", r.stdout)

    def test_integer_boundaries(self):
        r = self.run_model((ROOT / "short-tests/types/types00.smv").read_text())
        self.assertIn("consistency check failed", r.stdout)

    def test_mixed_comparisons(self):
        # Each expression has mixed signedness, including nested cached DEFINEs.
        for comparison in ("a > b", "b < a", "a >= b", "b <= a"):
            with self.subTest(comparison=comparison):
                r = self.run_model("#word-width 8\nMODULE main\nVAR a:uint8; b:int8;\n"
                                   "INIT a=1 && b=0;\nDEFINE p := " + comparison + ";\nINVAR p;\n")
                self.assertIn("consistency check ok", r.stdout)

    def test_widening_uses_source_signedness(self):
        r = self.run_model("#word-width 16\nMODULE main\nVAR u:uint8; s:int8;\n"
                           "INIT u=(uint8)200 && s=(int8)-50;\n"
                           "INVAR (int16)u=200 && (uint16)s=(uint16)-50;\n")
        self.assertIn("consistency check ok", r.stdout)

    def test_overlapping_guards_invalidate_model(self):
        r = self.run_model("MODULE main\n#inertial\nVAR x:boolean;\nINIT !x;\n"
                           "TRANS TRUE ?: x:=TRUE;\nTRANS TRUE ?: x:=FALSE;\n",
                           "last\ncheck-trans\nquit\n", code=2)
        self.assertIn("UNSUCCESSFUL", r.stdout)
        self.assertIn("mutually exclusive", r.stderr)
        self.assertIn("No validated model", r.stderr)
        self.assertNotIn("consistency check ok", r.stdout)

    def test_exclusive_guards(self):
        r = self.run_model("MODULE main\n#inertial\nVAR x:boolean;\nINIT !x;\n"
                           "TRANS x ?: x:=FALSE;\nTRANS !x ?: x:=TRUE;\n", "check-trans\nquit\n")
        self.assertIn("consistency check ok", r.stdout)

    def test_guard_overlap_outside_invariant_is_rejected(self):
        r = self.run_model("MODULE main\n#inertial\nVAR x:boolean;\nINIT !x;\nINVAR !x;\n"
                           "TRANS TRUE ?: x:=TRUE;\nTRANS x ?: x:=FALSE;\n", code=2)
        self.assertIn("mutually exclusive", r.stderr)

    def test_guard_validation_cannot_be_disabled(self):
        r = self.run_model("MODULE main;", options=("--fsm-inertial-checks", "no"), code=2)
        self.assertIn("guard validation is required", r.stderr)

    def test_empty_reachability_portfolio(self):
        options = tuple(itertools.chain.from_iterable(
            ("--reach-" + name + "-strategy", "no")
            for name in ("forward", "backward", "fast-forward", "fast-backward")))
        r = self.run_model("MODULE main\nVAR x:boolean;\n", "reach x\nquit\n", options, code=2)
        self.assertIn("No compatible reachability strategy", r.stderr)

    def test_trailing_model_input_is_rejected(self):
        self.run_model("MODULE main\nVAR x:boolean;\nGARBAGE", code=2)

    def test_validation_and_batch_errors_are_sticky(self):
        for source in ("NOT_A_MODEL", "MODULE main\nVAR x:boolean;\nINIT missing;\n",
                       "MODULE main\nVAR x:boolean;\nINIT x + TRUE;\n"):
            with self.subTest(source=source):
                r = self.run_model(source, "check-init\necho \"after error\"\nquit\n", code=2)
                self.assertNotIn("consistency check ok", r.stdout)

    def test_command_parse_error_is_sticky(self):
        for command in ("not-a-command", "check-init ignored", "reach x -f TRUE"):
            self.run_model("MODULE main\nVAR x:boolean;\n", command + "\nquit\n", code=2)

    def test_eof_preserves_last_result(self):
        r = self.run_model("MODULE main\nVAR x:boolean;\nINIT FALSE;\n", "check-init\nlast\n")
        self.assertIn("UNSUCCESSFUL", r.stdout)

    def test_invalid_limits(self):
        for command in ("pick-state -l 0", "check-trans -l 0"):
            with self.subTest(command=command):
                self.run_model("MODULE main\nVAR x:boolean;\n", command + "\nquit\n", code=2)

    def test_state_count_excludes_whole_valuation(self):
        # Both unconstrained variables must be counted; frozen bits count too.
        for declaration in ("VAR x,y:boolean;", "VAR x:boolean;\n#frozen\nVAR y:boolean;"):
            r = self.run_model("MODULE main\n" + declaration + "\n", "pick-state -n\nquit\n")
            self.assertIn("has 4 feasible initial states", r.stdout)

    def test_limit_saves_witness_and_is_incomplete(self):
        r = self.run_model("MODULE main\nVAR x,y:boolean;\n",
                           "pick-state -a -l 1\nlist-traces\nlast\nquit\n", code=3)
        self.assertIn("incomplete", r.stdout)
        self.assertIn("sim-", r.stdout)

    def test_single_pick_does_not_claim_unique(self):
        r = self.run_model("MODULE main\nVAR x,y:boolean;\n", "pick-state\nquit\n")
        self.assertIn("at least one", r.stdout)

    def test_compound_command_preserves_inconclusive_result(self):
        r = self.run_model("MODULE main\nVAR x,y:boolean;\n",
                           'do pick-state -n -l 1; echo "should not execute";\nlast\nquit\n', code=3)
        self.assertNotIn("should not execute", r.stdout)
        self.assertIn("INCONCLUSIVE", r.stdout)

    def test_conditionals_preserve_inconclusive_result(self):
        r = self.run_model("MODULE main\nVAR x,y:boolean;\n",
                           'pick-state -n -l 1\non success echo "bad-success"\n'
                           'on failure echo "bad-failure"\nlast\nquit\n', code=3)
        self.assertNotIn("bad-success", r.stdout)
        self.assertNotIn("bad-failure", r.stdout)
        self.assertIn("INCONCLUSIVE", r.stdout)

    def test_nonsemantic_command_errors_are_sticky(self):
        for command in ('get missing', 'read-trace', 'read-trace "/missing-yasmv-trace"', 'reach'):
            with self.subTest(command=command):
                self.run_model("MODULE main\nVAR x:boolean;\n", command + '\necho "done"\nquit\n', code=2)

    def test_explicit_root_and_declaration_order(self):
        yes = "MODULE yes\nVAR x:boolean;\nINIT x;\n"
        no = "MODULE no\nVAR x:boolean;\nINIT FALSE;\n"
        for source in (yes + no, no + yes):
            self.run_model(source, code=2)
            self.run_model(source, options=("--root", "missing"), code=2)
            r = self.run_model(source, options=("--root", "yes"))
            self.assertIn("consistency check ok", r.stdout)
            r = self.run_model(source, options=("--root", "no"))
            self.assertIn("consistency check failed", r.stdout)

    def test_model_replacement_is_rejected(self):
        r = self.run_model("MODULE main\nVAR x:boolean;\nINIT x;\n",
                           'read-model "missing.smv"\ncheck-init\nquit\n', code=2)
        self.assertIn("Model replacement", r.stderr)
        self.assertIn("consistency check ok", r.stdout)

    def test_long_and_empty_command_lines(self):
        r = self.run_model("MODULE main\nVAR x:boolean;\n",
                           '\n# comment\necho "' + 'a' * 1500 + '"\ncheck-init\nquit\n')
        self.assertIn('a' * 1500, r.stdout)
        self.assertIn("consistency check ok", r.stdout)


class HarnessTests(unittest.TestCase):
    def test_harness_rejects_false_success(self):
        for script in ("run-short-tests.sh", "run-functional-tests.sh"):
            for body in ("echo KO", "echo OK; exit 7", "kill -SEGV $$", "sleep 2"):
                with self.subTest(script=script, body=body), tempfile.TemporaryDirectory() as directory:
                    fake = Path(directory) / "fake-checker"
                    fake.write_text("#!/bin/bash\nulimit -c 0\n" + body + "\n")
                    fake.chmod(0o755)
                    result = subprocess.run(["bash", str(ROOT / "tools" / script)],
                                            cwd=ROOT, text=True, capture_output=True, timeout=10,
                                            env=dict(ENV, YASMV=str(fake), YASMV_TEST_TIMEOUT="0.1"))
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn("FAILED", result.stdout)


if __name__ == "__main__":
    unittest.main()
