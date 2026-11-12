"""Reject unregistered declarations, proof escapes and unsound reports in the pilot-onset audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_pilot_onset as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PilotOnsetAuditTests(unittest.TestCase):
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
        # The onset condition, with the cube and the quantile threshold as the core scale.
        self.assertIn("2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 ≤ "
                      "Real.sqrt ρ", source)
        self.assertIn("∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → PilotOnset μ ρ J", source)
        self.assertIn("{J : ℕ} (h : PilotOnset μ ρ J),\n    TailOnset μ ρ J", source)
        # The split: both parts, the mass of the quantile part and the positive threshold.
        self.assertIn("quantileTail μ ρ + quantileCore μ ρ = μ ∧", source)
        self.assertIn("quantileTail μ ρ Set.univ = ENNReal.ofReal ρ ∧", source)
        self.assertIn("0 < quantileThreshold μ ρ ∧", source)
        self.assertIn("∀ᵐ d : Gap ∂quantileCore μ ρ, quantileThreshold μ ρ ≤ (d : ℝ)", source)
        # (A12): both parts at every depth 1 <= j <= J, with the pilot's own budgets.
        self.assertIn("{J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J)", source)
        self.assertIn("(∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ) / "
                      "(pilotBudget J j : ℝ) ≤\n"
                      "      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J)", source)
        self.assertIn("(∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ) / "
                      "(pilotBudget J j : ℝ) ≤\n"
                      "      2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / "
                      "(quantileThreshold μ ρ) ^ 2", source)
        # The oracle forms: the rarity range, the onset hypothesis and the constants.
        self.assertIn("(hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) "
                      "(hon : PilotOnset μ ρ J)", source)
        self.assertIn("8193 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        self.assertIn("ENNReal.ofReal (16 / (pilotCoinCap J ρ : ℝ)) ≤ "
                      "ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        self.assertIn("ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) ≤ "
                      "ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        self.assertIn("1 / (pilotCoinCap J ρ : ℝ) ≤ Real.sqrt ρ * (1 / 2) ^ J / 8", source)
        # The kernel facts behind (A12).
        self.assertIn("tailWorkEnvelope j d ≤ 2048 * 4 ^ j * min 1 ((1 / 2) ^ j / (d : ℝ))", source)
        self.assertIn("{a : ℝ} (ha : 0 < a) (d : Gap) (had : a ≤ (d : ℝ)),\n"
                      "    tailWorkEnvelope j d ≤ 1024 * ((j : ℝ) + 1) / a ^ 2", source)
        self.assertIn("{t s : ℝ} (ht : 0 < t) (hts : t ≤ s)", source)

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
