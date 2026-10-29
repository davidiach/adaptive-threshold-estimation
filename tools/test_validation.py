"""Failure-path regressions for the frozen scorer, numeric coverage and 713 lock."""
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
import re
import runpy
import sys
import tempfile
import unittest
from unittest.mock import patch

import numpy as np

import score
import verify_uniform713 as uniform713
import verify_experiment_lock as experiment_lock
import verify_uniform_arithmetic as arithmetic

ROOT = Path(__file__).resolve().parents[1]


class ScorerTests(unittest.TestCase):
    def test_unicode_lean_output_with_windows_default_encoding(self):
        expected = "Lean diagnostic: \u2190 \u03a9 \u26a0\n"
        command = [sys.executable, "-c",
                   f"import sys; sys.stdout.buffer.write({expected.encode('utf-8')!r})"]
        # Emulate the cp1252 default even on Linux CI; the scorer must request
        # UTF-8 explicitly for Lean's output (U+2190 contains byte 0x90).
        with patch("subprocess._text_encoding", return_value="cp1252"):
            rc, output = score.run(command, 30)
        self.assertEqual(rc, 0)
        self.assertEqual(output, expected)

    def simulate(self, *, audit_rc=0, missing=False, axioms=None, error=False):
        targets = score.TARGETS["targets"]
        subject = next(t["name"] for t in targets if t.get("tier", 1) == 2)
        spans = {t["name"]: (5 + 3 * i, 7 + 3 * i) for i, t in enumerate(targets)}
        lines = []
        for t in targets:
            name = t["name"]
            if name == subject and missing:
                continue
            deps = ["propext", "Classical.choice", "Quot.sound"]
            if t.get("tier", 1) == 2:
                deps.append("sorryAx")
            if name == subject and axioms is not None:
                deps = axioms
            lines.append(f"'ThresholdHCAudit.audit_{name}' depends on axioms: [{', '.join(deps)}]")
        if error:
            lines.append(f".audit/Audit.lean:{spans[subject][0]}:0: error: type mismatch")
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(score, "RESULTS", Path(directory)), \
                 patch.object(score, "check_frozen", return_value=(True, [])), \
                 patch.object(score, "scan_forbidden", return_value=[]), \
                 patch.object(score, "write_audit", return_value=(score.LEAN / ".audit/Audit.lean", spans)), \
                 patch.object(score, "run", return_value=(audit_rc, "\n".join(lines))), \
                 patch("sys.argv", ["score.py", "--no-build"]), redirect_stdout(io.StringIO()):
                rc = score.main()
            result = json.loads((Path(directory) / "lean_score.json").read_text())
        return rc, result, result["targets"][subject]

    def test_valid_tier2_baseline(self):
        rc, result, _ = self.simulate()
        self.assertEqual(rc, 0)
        self.assertTrue(result["valid"])
        self.assertEqual(result["points_by_tier"], {"1": {"points": 60, "max": 60},
                                                   "2": {"points": 0, "max": 61}})

    def test_invalid_audits_zero_score(self):
        cases = [dict(audit_rc=1), dict(missing=True), dict(error=True),
                 dict(axioms=["UnexpectedAxiom"]),
                 dict(axioms=["sorryAx", "UnexpectedAxiom"]),
                 dict(axioms=["UnexpectedAxiom", "sorryAx"])]
        for case in cases:
            with self.subTest(case=case):
                rc, result, _ = self.simulate(**case)
                self.assertNotEqual(rc, 0)
                self.assertFalse(result["valid"])
                self.assertEqual(result["points"], 0)

    def test_mixed_axiom_report_is_a_violation(self):
        _, result, target = self.simulate(axioms=["propext", "sorryAx", "UnexpectedAxiom"])
        self.assertEqual(target["status"], "violation")
        self.assertTrue(result["violations"])


class NumericCoverageTests(unittest.TestCase):
    def test_all_targets_have_real_checks(self):
        with redirect_stdout(io.StringIO()):
            scope = runpy.run_path(str(ROOT / "tools/check_targets2_numeric.py"))
        self.assertEqual(len(scope["names"]), 13)
        self.assertTrue(all(scope["counts"].get(n, 0) > 0 for n in scope["names"]))
        self.assertGreater(scope["counts"]["stopped_transcript_testing"], 0)

    def test_zero_i6_coverage_fails(self):
        path = ROOT / "tools/check_targets2_numeric.py"
        source = path.read_text(encoding="utf-8")
        # Suppress I6 observations at the recording boundary, without altering
        # the reporting code. A synthetic passing fallback must not mask this.
        original = "def record(name, margin):\n"
        self.assertEqual(source.count(original), 1)
        source = source.replace(original, original +
                                '    if name == "stopped_transcript_testing":\n        return\n')
        output = io.StringIO()
        with redirect_stdout(output), self.assertRaises(SystemExit) as raised:
            exec(compile(source, str(path), "exec"), {"__file__": str(path)})
        self.assertEqual(raised.exception.code, 1)
        self.assertIn("UNCHECKED TARGETS: ['stopped_transcript_testing']", output.getvalue())
        self.assertNotIn("All 13", output.getvalue())


class Uniform713LockTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((ROOT / "tools/uniform713_targets.json").read_text())

    def test_current_sources_match(self):
        locked = uniform713.check_specification_lock(self.manifest)
        self.assertEqual(set(locked), uniform713.DEFINITION_SOURCES | {uniform713.SPECIFICATION})

    def test_missing_or_partial_manifest_fails(self):
        for removed in [None, *uniform713.DEFINITION_SOURCES]:
            with self.subTest(removed=removed):
                manifest = copy.deepcopy(self.manifest)
                if removed is None:
                    manifest.pop("definition_sources_sha256")
                else:
                    manifest["definition_sources_sha256"].pop(removed)
                with self.assertRaises(SystemExit):
                    uniform713.check_specification_lock(manifest)

    def test_every_locked_source_rejects_changes_and_deletion(self):
        locked = uniform713.check_specification_lock(self.manifest)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for rel in locked:
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((ROOT / rel).read_bytes())
            for rel in locked:
                with self.subTest(source=rel):
                    path = root / rel
                    original = path.read_bytes()
                    path.write_bytes(original + b"\n-- changed definition file\n")
                    with self.assertRaises(SystemExit):
                        uniform713.check_specification_lock(self.manifest, root)
                    path.unlink()
                    with self.assertRaises(SystemExit):
                        uniform713.check_specification_lock(self.manifest, root)
                    path.write_bytes(original)

    def test_locks_cover_local_import_closure(self):
        pending = [uniform713.SPECIFICATION]
        visited = set()
        while pending:
            rel = pending.pop()
            if rel in visited:
                continue
            visited.add(rel)
            source = (ROOT / rel).read_text(encoding="utf-8")
            for module in re.findall(r"^import\s+(ThresholdHC[\w.]*)\s*$", source, re.M):
                pending.append("lean/" + module.replace(".", "/") + ".lean")
        self.assertEqual(visited, uniform713.DEFINITION_SOURCES | {uniform713.SPECIFICATION})


class UniformArithmeticAuditTests(unittest.TestCase):
    def setUp(self):
        self.lines = [f"'ThresholdHC.PaperConstants.{name}' depends on axioms: [propext]"
                      for name in sorted(arithmetic.NAMES)]

    def test_recorded_audit_and_current_source_pass(self):
        log = (ROOT / "results/constants_uniform_lean_audit.log").read_text(encoding="utf-8")
        self.assertTrue(arithmetic.check(log, 0)[0])
        source = arithmetic.SOURCE.read_text(encoding="utf-8")
        self.assertIsNone(arithmetic.FORBIDDEN.search(arithmetic.strip_comments(source)))

    def test_later_duplicate_cannot_overwrite_a_bad_report(self):
        bad = [line.replace("[propext]", "[propext, sorryAx]") for line in self.lines]
        clean = [line.replace("depends on axioms: [propext]", "does not depend on any axioms")
                 for line in self.lines]
        self.assertTrue(arithmetic.check("\n".join(clean), 0)[0])
        self.assertFalse(arithmetic.check("\n".join(bad + clean), 0)[0])

    def test_sorry_warning_failure_and_missing_lemma_rejected(self):
        for output, returncode in (
                ("\n".join(self.lines + ["warning: declaration uses `sorry`"]), 0),
                ("\n".join(self.lines), 1), ("\n".join(self.lines[1:]), 0)):
            with self.subTest(output=output[-40:], returncode=returncode):
                self.assertFalse(arithmetic.check(output, returncode)[0])


class ExperimentLockTests(unittest.TestCase):
    def setUp(self):
        self.hashes = json.loads((ROOT / "results/real_selection.json").read_text())["hashes"]

    def locked(self, name):
        return (ROOT / name).read_bytes(), self.hashes[name]

    def test_rewritten_record_may_differ_only_in_line_endings(self):
        name = "results/real_verification.json"
        # CI runs verify_real.py first, so the checkout may already hold either form.
        data, expected = self.locked(name)
        lf = data.replace(b"\r\n", b"\n")
        crlf = lf.replace(b"\n", b"\r\n")
        self.assertNotEqual(lf, crlf)
        for form in (lf, crlf):
            self.assertTrue(experiment_lock.matches_lock(name, form, expected))
            self.assertFalse(experiment_lock.matches_lock(
                name, form.replace(b"true", b"false"), expected))
        # Stray carriage returns are content, not a line-ending convention.
        self.assertFalse(experiment_lock.matches_lock(name, lf.replace(b"\n", b"\r\r\n"), expected))
        self.assertFalse(experiment_lock.matches_lock(name, lf.replace(b"\n", b"\r\n", 1), expected))

    def test_strict_mode_requires_the_exact_committed_bytes(self):
        # CI checks the committed tree with --strict, so a commit converting the
        # locked record to LF fails there even though a local rewrite is tolerated.
        name = "results/real_verification.json"
        data, expected = self.locked(name)
        crlf = data.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
        self.assertTrue(experiment_lock.matches_lock(name, crlf, expected, strict=True))
        self.assertFalse(experiment_lock.matches_lock(name, crlf.replace(b"\r\n", b"\n"), expected, strict=True))

    def test_other_locked_files_must_match_byte_for_byte(self):
        name = "benchmark/verify_real.py"
        data, expected = self.locked(name)
        self.assertTrue(experiment_lock.matches_lock(name, data, expected))
        self.assertFalse(experiment_lock.matches_lock(name, data.replace(b"\n", b"\r\n"), expected))

    def heldout(self):
        test = json.loads((ROOT / "results/real_test.json").read_text())
        training = json.loads((ROOT / "benchmark/data/training.json").read_text())["training"]
        with np.load(ROOT / "results/real_test_raw.npz") as raw:
            return json.loads((ROOT / "results/real_selection.json").read_text()), test, dict(raw), training

    def test_heldout_record_is_recomputed_from_raw_data(self):
        lock, test, raw, training = self.heldout()
        self.assertIs(experiment_lock.check_heldout(lock, test, raw, training), False)

    def test_heldout_record_mutations_rejected(self):
        # The external review's four mutations, each of which the old guard accepted.
        def flipped(test, raw):
            test["accept"] = True

        def emptied(test, raw):
            test["rows"], test["accept"] = [], True

        def repeated(test, raw):
            test["rows"] = [test["rows"][0]] * 4

        def unseeded(test, raw):
            for row in test["rows"]:
                row["seed"], row["config"] = 0, {}

        def extra_array(test, raw):
            raw["extra_value"] = raw["gha_tuned_16384_value"]

        def changed_value(test, raw):
            raw["real_tuned_16384_value"] = raw["real_tuned_16384_value"].copy()
            raw["real_tuned_16384_value"][0] += 0.5

        def reshaped_interval(test, raw):
            test["rows"][0]["rmse_interval"] = [test["rows"][0]["rmse_interval"]] * 2

        lock, test, raw, training = self.heldout()
        for mutate in (flipped, emptied, repeated, unseeded, extra_array, changed_value,
                       reshaped_interval):
            changed, changed_raw = copy.deepcopy(test), dict(raw)
            mutate(changed, changed_raw)
            with self.subTest(mutation=mutate.__name__), self.assertRaises(RuntimeError):
                experiment_lock.check_heldout(lock, changed, changed_raw, training)

    def test_sealed_results_and_start_record_are_pinned(self):
        experiment_lock.check_sealed()
        real = experiment_lock.digest
        for name, message in (("results/real_test_raw.npz", "sealed held-out result changed"),
                              ("results/real_test.json", "sealed held-out result changed"),
                              ("results/real_selection.json", "test start record")):
            def changed(path, name=name):
                return "0" * 64 if path == name else real(path)
            with self.subTest(name=name), patch.object(experiment_lock, "digest", changed), \
                    self.assertRaisesRegex(RuntimeError, message):
                experiment_lock.check_sealed()

    def test_lock_check_passes_after_a_linux_rewrite(self):
        record = ROOT / "results/real_verification.json"
        read_bytes = Path.read_bytes

        def rewritten(path):
            data = read_bytes(path)
            return data.replace(b"\r\n", b"\n") if path == record else data

        with patch.object(Path, "read_bytes", rewritten), redirect_stdout(io.StringIO()) as output:
            experiment_lock.main([])
        self.assertIn("Verified 9 benchmark locks", output.getvalue())
        with patch.object(Path, "read_bytes", rewritten), self.assertRaises(SystemExit):
            experiment_lock.main(["--strict"])


if __name__ == "__main__":
    unittest.main()
