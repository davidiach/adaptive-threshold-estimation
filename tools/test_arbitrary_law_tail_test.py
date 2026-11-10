"""Reject unregistered declarations, proof escapes and unsound reports in the tail-test audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_tail_test as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class TailTestAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_statements_carry_their_constants_and_hypotheses(self):
        source, _ = audit.audit_input()
        # The integer threshold, the strict stopping inequality and the stopping rule.
        self.assertIn("tailThreshold J k = ⌈Real.sqrt (tailScale J k)⌉₊", source)
        self.assertIn("tailScale J k = 2 * 4 ^ k * (J - k + 2)", source)
        self.assertIn("2 * (tailThreshold J k : ℤ) < |2 * (tailHeads (4 ^ k) ω : ℤ)", source)
        self.assertIn("tailStop J ω = sInf {k | J ≤ k ∨ tailResolvedAt J k ω}", source)
        # The small-gap and large-gap hypotheses and the three bounds.
        self.assertIn("(hd : (d : ℝ) ≤ (1 / 2) ^ J)", source)
        self.assertIn("(hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ))", source)
        self.assertIn("exp (-(4 ^ J * (d : ℝ) ^ 2 / 2))", source)
        self.assertIn("min (4 ^ J) (1024 / d ^ 2 * (1 + tailLog J d))", source)
        self.assertIn("min 1 (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2)", source)
        # Sign neutrality is stated for every sign law of the original population.
        self.assertIn("(q : SignLaw)", source)
        self.assertIn("originalPopulationTapeLaw μ q", source)
        self.assertIn("(μ.prod lightMultiplier)", source)

    def test_unregistered_declaration_rejected(self):
        with patch.object(audit, "declared_names", return_value=audit.NAMES + ["extra_lemma"]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()
        with patch.object(audit, "declared_names", return_value=audit.NAMES[1:]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()

    def test_proof_escape_rejected(self):
        escaped = lambda source: source + "\ntheorem hidden : False := by sorry\n"
        with patch.object(audit, "strip_comments", side_effect=escaped):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.declared_names()

    def test_missing_or_unsound_report_rejected(self):
        _, roots = audit.audit_input()
        missing = sorted(roots)[1:]
        with self.assertRaises(ValueError):
            shared.validate_reports(report(missing), 0, roots)
        with self.assertRaises(ValueError):
            shared.validate_reports(report(roots, "propext, sorryAx"), 0, roots)
        with self.assertRaises(ValueError):
            shared.validate_reports(report(roots), 1, roots)


if __name__ == "__main__":
    unittest.main()
