"""Reject unregistered declarations, proof escapes and unsound reports in the tail-oracle audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_tail_oracle as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class TailOracleAuditTests(unittest.TestCase):
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
        # The kernel and the onset condition, with the quantile threshold as the core scale.
        self.assertIn("tailUnresolvedProb J d + tailWorkEnvelope J d / 4 ^ J", source)
        self.assertIn("2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 ≤ "
                      "Real.sqrt ρ", source)
        # The two kernel bounds.
        self.assertIn("tailOracleKernel J d ≤ 2052 * min 1 ((1 / 2) ^ J / (d : ℝ))", source)
        self.assertIn("{a : ℝ} (ha : 0 < a) (d : Gap) (had : a ≤ (d : ℝ))", source)
        self.assertIn("(1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / a ^ 2", source)
        # The comparison constants and the rarity range.
        self.assertIn("(hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hon : TailOnset μ ρ J)", source)
        self.assertIn("4096 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        self.assertIn("524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        # The onset exists and is chosen before the sign law's parameters of the run.
        self.assertIn("∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → TailOnset μ ρ J", source)
        self.assertIn("∃ J₀ : ℕ, ∀ (J m : ℕ) (δ : ℝ), J₀ ≤ J → 0 < m → 0 < δ → "
                      "8 * log (2 / δ) ≤ m →", source)
        # Statement (3): coverage for every choice of budgets, and the oracle bound.
        self.assertIn("(hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J)", source)
        self.assertIn("ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) ω) ≤",
                      source)
        self.assertIn("(TailOnset μ ρ J →", source)
        self.assertIn("(J₀ ≤ J →", source)
        self.assertIn("(fun j i => ω (Nat.pair J (Nat.pair j i)))", source)
        self.assertIn("(q : SignLaw)", source)

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
