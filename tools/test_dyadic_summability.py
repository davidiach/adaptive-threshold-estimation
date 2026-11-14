"""Reject unregistered declarations, proof escapes and unsound reports in the dyadic-summability audit."""
import unittest
from unittest.mock import patch

import verify_dyadic_summability as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class DyadicSummabilityAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(roots, {"ThresholdHC.Proofs." + name for name in audit.NAMES})
        # Five restated theorems and the two frozen targets they complete.
        self.assertEqual(source.count("example "), len(audit.NAMES) + 2)
        shared.validate_reports(report(roots), 0, roots)

    def test_both_series_converge_to_the_frozen_bounds(self):
        source, _ = audit.audit_input()
        self.assertIn("∃ s, HasSum (fun k : ℕ => (2:ℝ)^k * Real.exp (-(b*2^k))) s ∧ s ≤ 2 / b",
                      source)
        self.assertIn("∃ s, HasSum (fun k : ℕ => ((2:ℝ)^k)^2 * Real.exp (-(b*2^k))) s ∧ "
                      "s ≤ 8 / (3 * b^2)", source)
        self.assertIn("example : ThresholdHC.Targets.dyadic_sum_v1 ↔", source)
        self.assertIn("example : ThresholdHC.Targets.dyadic_sum_v2 ↔", source)

    def test_unregistered_declaration_rejected(self):
        with patch.object(audit, "declared_names", return_value=audit.NAMES + ["extra"]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()

    def test_proof_escape_rejected(self):
        with patch.object(audit, "strip_comments",
                          side_effect=lambda s: s + "\ntheorem t : False := by sorry\n"):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.declared_names()

    def test_missing_or_unsound_report_rejected(self):
        _, roots = audit.audit_input()
        for output, code in ((report(sorted(roots)[1:]), 0), (report(roots, "sorryAx"), 0),
                             (report(roots), 1)):
            with self.assertRaises(ValueError):
                shared.validate_reports(output, code, roots)


if __name__ == "__main__":
    unittest.main()
