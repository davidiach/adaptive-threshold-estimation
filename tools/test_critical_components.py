"""Negative acceptance cases for the new component axiom audit."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

import verify_critical_components as critical

from verify_critical_components import (
    EXACT_TARGETS, ROOTS, SOURCE, exact_targets, strip_comments, validate_reports,
)


class CriticalComponentAuditTests(unittest.TestCase):
    def setUp(self):
        self.lines = [f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                      for name in sorted(ROOTS)]

    def test_complete_standard_axiom_reports_pass(self):
        self.assertEqual(set(validate_reports("\n".join(self.lines), 0, ROOTS)), ROOTS)

    def test_nonzero_exit_rejects_complete_looking_output(self):
        with self.assertRaises(ValueError):
            validate_reports("\n".join(self.lines), 1, ROOTS)

    def test_missing_duplicate_and_extra_roots_rejected(self):
        for lines in (self.lines[:-1], self.lines + self.lines[:1],
                      self.lines + ["'unexpected' does not depend on any axioms"]):
            with self.subTest(lines=lines), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0, ROOTS)

    def test_unproved_and_nonstandard_axioms_rejected(self):
        for axiom in ("sorryAx", "untrusted_assumption"):
            lines = self.lines.copy()
            lines[0] = lines[0].replace("[propext,", f"[{axiom}, propext,")
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0, ROOTS)


class CriticalExactTargetTests(unittest.TestCase):
    def setUp(self):
        self.audit = (SOURCE / "Audit.lean").read_text(encoding="utf-8")
        self.check = "example : CriticalMinimaxLowerStatement := critical_minimax_lower_bound"

    def test_audit_checks_every_specification_statement(self):
        self.assertEqual(len(EXACT_TARGETS), 43)
        self.assertEqual(exact_targets(strip_comments(self.audit)), EXACT_TARGETS)

    def test_removed_commented_or_duplicate_check_rejected(self):
        for audit in (self.audit.replace(self.check, ""),
                      self.audit.replace(self.check, "-- " + self.check),
                      self.audit + "\n" + self.check + "\n"):
            with self.subTest(audit=audit[-80:]), self.assertRaises(ValueError):
                exact_targets(strip_comments(audit))

    def test_suppressed_target_failures_rejected_before_running_lean(self):
        # Both forms preserve target coverage and can make Lean exit successfully
        # without proving this example. Reject the source before trusting its log.
        replacements = (
            "#guard_msgs (drop all) in\n"
            "example : CriticalMinimaxLowerStatement := by trivial",
            "#guard_msgs (error, drop warning) in\n"
            "example : CriticalMinimaxLowerStatement := by stop rfl",
        )
        read_text = Path.read_text
        for replacement in replacements:
            changed = self.audit.replace(self.check, replacement)
            self.assertEqual(exact_targets(strip_comments(changed)), EXACT_TARGETS)

            def read_source(path, *args, **kwargs):
                if path == SOURCE / "Audit.lean":
                    return changed
                return read_text(path, *args, **kwargs)

            with self.subTest(replacement=replacement), TemporaryDirectory() as temporary:
                with patch.object(Path, "read_text", read_source), \
                        patch("sys.argv", ["verify_critical_components.py", "--output-dir",
                                           str(Path(temporary) / "evidence")]), \
                        patch.object(critical.subprocess, "run", side_effect=AssertionError(
                            "Suppressed proof failures must be rejected before invoking Lean")) as run:
                    with self.assertRaisesRegex(ValueError, "Forbidden proof escape in Audit.lean"):
                        critical.main()
                    run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
