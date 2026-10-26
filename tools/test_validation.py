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

import score
import verify_uniform713 as uniform713

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


if __name__ == "__main__":
    unittest.main()
