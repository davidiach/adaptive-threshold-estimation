"""Negative acceptance cases for the new component axiom audit."""
import unittest

from verify_critical_components import ROOTS, validate_reports


class CriticalComponentAuditTests(unittest.TestCase):
    def setUp(self):
        self.lines = [f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                      for name in sorted(ROOTS)]

    def test_complete_standard_axiom_reports_pass(self):
        self.assertEqual(set(validate_reports("\n".join(self.lines), 0)), ROOTS)

    def test_nonzero_exit_rejects_complete_looking_output(self):
        with self.assertRaises(ValueError):
            validate_reports("\n".join(self.lines), 1)

    def test_missing_duplicate_and_extra_roots_rejected(self):
        for lines in (self.lines[:-1], self.lines + self.lines[:1],
                      self.lines + ["'unexpected' does not depend on any axioms"]):
            with self.subTest(lines=lines), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0)

    def test_unproved_and_nonstandard_axioms_rejected(self):
        for axiom in ("sorryAx", "untrusted_assumption"):
            lines = self.lines.copy()
            lines[0] = lines[0].replace("[propext,", f"[{axiom}, propext,")
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0)


if __name__ == "__main__":
    unittest.main()
