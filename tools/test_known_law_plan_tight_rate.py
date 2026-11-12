"""Reject unregistered declarations, proof escapes and unsound reports in the tight-rate audit."""
import unittest
from unittest.mock import patch

import verify_known_law_plan_tight_rate as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.KnownLawPlanner."
K = "ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B"
K_ZERO = "zeroSelection (zeroAtomLaw z₀ η) ρ B"
POSITIVE = "1 + 8/5 * max 4096 (224000 * sqrt θ)"
ZERO = "1 + 4 * max 4096 (224000 * sqrt θ)"
SCALED_SPLIT = ("(hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) "
                "(htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))")


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PlanTightRateAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_tight_contract_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # The contract: factor four for the entropy, factor two for the rest,
        # the last two at the powers of four only.
        self.assertIn(
            "E.Tight z ↔\n"
            "      (E.entropy ≤ 4 * costEntropy (fun j : Fin N => bandCost σ j.val) ∧\n"
            "      E.tailInverse ≤ 2 * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ∧\n"
            "      z ≤ E.unresolved ∧ E.unresolved ≤ 2 * z ∧\n"
            "      (∀ k : ℕ, E.resolvedError (4 ^ k) ≤ 2 * eta (σ+τ) (4 ^ k)) ∧\n"
            "      ∀ k : ℕ, E.tailWork (4 ^ k) ≤ 2 * ordinaryCost τ (4 ^ k)) :=\n"
            "  fun _ _ => Iff.rfl", source)
        self.assertIn("(SplitEnclosure.exact σ τ ζ N).Tight (ζ.real univ)", source)
        self.assertIn("(hE : E.Tight z),\n    EnvelopeVanishes E.resolvedError", source)
        # Band costs within a factor two give an entropy within a factor two.
        self.assertIn("(hab : ∀ j, a j ≤ b j) (hb : ∀ j, b j ≤ 2 * a j),\n"
                      "    costEntropy a ≤ costEntropy b ∧ costEntropy b ≤ 2 * costEntropy a",
                      source)
        # Caps and prices against the next level of the exact schedule.
        self.assertIn("searchCaps E.resolvedError hE.vanishes hρ l ≤\n"
                      "      errorCapExponent (σ+τ) (levelAccuracy ρ (l+1)) "
                      "(levelAccuracy_pos hρ (l+1))", source)
        self.assertIn("E.price ρ l (searchCaps E.resolvedError hE.vanishes hρ l) ≤\n"
                      "      4 * levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => "
                      "bandCost σ j.val)) z hρ\n      (l+1)", source)
        self.assertIn("(hM : 0 < M) (hMP : M ≤ P),\n    ordinaryCost τ M ≤ ordinaryCost τ P",
                      source)
        self.assertIn("(hm : 0 < (σ+τ).real univ) (l k : ℕ),\n    0 < E.price ρ l k", source)

    def test_multilevel_sum_and_terminal_rule_carry_their_constants(self):
        source, _ = audit.audit_input()
        # No probability measure is assumed; the unresolved mass is a parameter.
        self.assertIn("(hm : ρ/128 < (σ+τ).real univ) (E : SplitEnclosure σ τ ζ N) "
                      "(hE : E.Tight z) (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/128),", source)
        self.assertIn("224000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +\n"
                      "      ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)", source)
        self.assertIn("levelAccuracy ρ J + sqrt θ * (224000*(sqrt (ρ*costEntropy\n"
                      "      (fun j : Fin N => bandCost σ j.val)) + ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) "
                      "/ sqrt B", source)
        self.assertIn("sqrt (planCertificate ρ (planRates B k w)) ≤ "
                      "levelAccuracy ρ J + sqrt θ * S / sqrt B", source)
        # The terminal level is chosen from the enclosure's unresolved mass.
        self.assertIn("(hz : 2048*E.unresolved ≤ ρ),\n"
                      "    z ≤ levelAccuracy ρ (planTerminal hρ B E.unresolved)/128 ∧\n"
                      "      levelAccuracy ρ (planTerminal hρ B E.unresolved) < "
                      "4096*z + ρ/(1+sqrt B)", source)
        # The arithmetic of the rate and of the fallback.
        self.assertIn("(hQ : min ρ (z + V) ≤ c * K) (hδ : δ ≤ m * z + F) (hs : s ≤ δ + a * V),\n"
                      "    min (ρ/2) s ≤ (1 + c * max m a) * K", source)
        self.assertIn("(hzU : z ≤ U) (hQ : min ρ U ≤ c * K) (hfall : ρ < m * z),\n"
                      "    ρ/2 ≤ (1 + c * max m a) * K", source)

    def test_positive_gap_rate_is_restated_in_full(self):
        source, _ = audit.audit_input()
        self.assertIn("(hcore : σ = quantileCore (σ+τ+ζ) ρ) "
                      "(htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) "
                      "(hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) "
                      "(hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)", source)
        self.assertIn("(E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) "
                      "(hz : 2048 * E.unresolved ≤ ρ)", source)
        self.assertEqual(source.count(f"ENNReal.ofReal ({POSITIVE}) *\n      {K}"), 2)
        self.assertIn("(hE : E.Tight (ζ.real univ)) (hz : ρ < 2048 * E.unresolved),\n"
                      f"    ENNReal.ofReal (ρ/2) ≤\n      ENNReal.ofReal ({POSITIVE}) *", source)
        self.assertIn(f"ENNReal.ofReal (6 * ({POSITIVE})) *\n      {K}", source)

    def test_zero_atom_rate_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # The floor and the design value of a law with mass at zero.
        self.assertIn("(hρ : 0 < ρ) (hρ2 : ρ ≤ 1/2) (hB : 0 < B),\n"
                      "    ENNReal.ofReal (ρ/(1+sqrt B)) ≤ zeroSelection (zeroAtomLaw z η) ρ B",
                      source)
        self.assertIn("zeroQuantileValue z₀ η ρ B =\n"
                      "      ENNReal.ofReal (min ρ (z₀ + ζ.real univ + budgetScale B * "
                      "(∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +\n"
                      "      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)))", source)
        self.assertIn(f"∃ K : ℝ, 0 ≤ K ∧ {K_ZERO} = ENNReal.ofReal K ∧\n"
                      "      ρ/(1+sqrt B) ≤ K ∧", source)
        self.assertIn("budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) ≤ 4 * K",
                      source)
        # The split is the scaled quantile split at the conditional rarity, and
        # the mass at zero is part of the unresolved mass of the design.
        self.assertEqual(source.count(SCALED_SPLIT), 6)
        self.assertEqual(source.count("(hE : E.Tight (z₀ + ζ.real univ))"), 4)
        self.assertEqual(source.count(
            "(hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))"), 3)
        self.assertEqual(source.count(f"ENNReal.ofReal ({ZERO}) *\n      {K_ZERO}"), 2)
        self.assertIn("(hE : E.Tight (z₀ + ζ.real univ)) (hz : ρ < 2048 * E.unresolved),\n"
                      f"    ENNReal.ofReal (ρ/2) ≤\n      ENNReal.ofReal ({ZERO}) *", source)
        # The planned coefficient and the radius for dyadic weights.
        self.assertIn("plannedCoefficient Csum = 1 + 4 * max 4096 (8 * sqrt 2 * Csum)", source)
        self.assertIn("plannedCoefficient C ≤ plannedCoefficient C'", source)
        self.assertEqual(source.count("(hup : ∀ i, w i ≤ 2 * sqrt (17*levelAccuracy ρ i.val"), 2)
        self.assertIn(f"ENNReal.ofReal (plannedCoefficient 28000) * {K_ZERO}", source)
        self.assertIn(f"ENNReal.ofReal (6 * plannedCoefficient 28000) * {K_ZERO}", source)

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
