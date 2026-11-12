"""Reject unregistered declarations, proof escapes and unsound reports in the planner-output audit."""
import unittest
from unittest.mock import patch

import verify_known_law_planner_output as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.KnownLawPlanner."
K = "ThresholdHC.EntropyTail.selection"
SPLIT = ("(hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) "
         "(hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) "
         "(hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)")


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PlannerOutputAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_constructed_splits_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # The cut at a gap: two finite parts with the stated supports.
        self.assertIn("∃ τ ζ : Measure Gap, IsFiniteMeasure τ ∧ IsFiniteMeasure ζ ∧ τ+ζ = ν ∧\n"
                      "      (∀ᵐ d : Gap ∂τ, h ≤ (d:ℝ)) ∧ (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ h)", source)
        # The quantile split of every law: it sums to the law and meets the
        # hypotheses of the rate theorems.
        self.assertIn("[IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ),\n"
                      "    ∃ σ τ ζ : Measure Gap, IsFiniteMeasure σ ∧ IsFiniteMeasure τ ∧ "
                      "IsFiniteMeasure ζ ∧\n"
                      "      σ+τ+ζ = μ ∧ σ = quantileCore μ ρ ∧ τ+ζ = quantileTail μ ρ ∧\n"
                      "      (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) ∧ "
                      "(∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)", source)
        # The design of a reference law with mass at zero.
        self.assertIn("{z₀ ρ : ℝ} (hzρ : z₀ < ρ) (hρ1 : ρ ≤ 1) (B : ℝ),\n"
                      "    ∃ σ τ ζ : Measure Gap, IsFiniteMeasure σ ∧ IsFiniteMeasure τ ∧ "
                      "IsFiniteMeasure ζ ∧\n"
                      "      σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀) ∧\n"
                      "      τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) ∧",
                      source)
        # Its exact enclosure: the mass at zero is added to the unresolved mass.
        self.assertIn("(SplitEnclosure.exactZero σ τ ζ N hz₀).unresolved = z₀ + ζ.real univ ∧",
                      source)
        self.assertIn("(SplitEnclosure.exactZero σ τ ζ N hz₀).resolvedError = eta (σ+τ) ∧", source)
        self.assertIn("fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩", source)
        self.assertIn("{z₀ : ℝ} (hz₀ : 0 ≤ z₀),\n"
                      "    (SplitEnclosure.exactZero σ τ ζ N hz₀).Tight (z₀ + ζ.real univ)", source)

    def test_end_to_end_rates_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # Validity in minimax form, for any enclosure with a vanishing envelope.
        self.assertIn("(E : SplitEnclosure σ τ ζ N) (hvan : EnvelopeVanishes E.resolvedError) "
                      "{J : ℕ} (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) "
                      "(hw : ∀ i, 0 < w i),\n"
                      "    rareMinimaxRisk (σ+τ+ζ) ρ B ≤\n"
                      "      ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ\n"
                      "      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) "
                      "w))))", source)
        # From upper bounds: no fallback hypothesis, both cases are covered.
        self.assertEqual(source.count(SPLIT), 2)
        self.assertIn("(E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) "
                      "(w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)", source)
        self.assertIn("rareMinimaxRisk (σ+τ+ζ) ρ B ≤\n"
                      "      ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *\n"
                      f"      {K} (σ+τ+ζ) ρ B", source)
        # Exact integrals and optimal weights, for every law.
        self.assertIn(f"ENNReal.ofReal 44801 * {K} (σ+τ+ζ) ρ B", source)
        self.assertIn("(μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hρ : 0 < ρ) "
                      "(hρ4 : ρ ≤ 1/4) (hB : 0 < B),\n"
                      f"    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 44801 * {K} μ ρ B", source)

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
