"""Reject unregistered declarations, proof escapes and unsound reports in the robust-plan audit."""
import unittest
from unittest.mock import patch

import verify_robust_plan as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.RobustContinuation."
TRUE_LAW = ("(π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) "
            "(href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) "
            "[IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] "
            "(hμ : μ = π.map Prod.snd + μ₀)")
ESTIMATOR = "robustPlanEstimator η σ ht hs hN hc hρc κ r"
EVERY_TRUE_LAW = (
    "    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),\n"
    "      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]\n"
    "      [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],\n"
    "      (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →\n"
    "      μ = π.map Prod.snd + μ₀ →\n"
    "      RareBudget μ A ρ B ∧\n"
    "      rareRisk μ A ρ ≤\n"
    "      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B")


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class RobustPlanAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_definitions_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # The level race is designed from the reference alone: null law eta,
        # positive allowance rho eps_l / c, cap 4^(kappa l).
        self.assertIn("(robustFamily η w hw hc hρc κ l).cost =\n"
                      "      raceCost (negativeBankTest w (levelEpsilon l))\n"
                      "        (positiveBankTest η w (ρ*levelEpsilon l/c)) (2 * κ l) ∧", source)
        self.assertIn("(robustFamily η w hw hc hρc κ l).value =\n"
                      "      raceValue (negativeBankTest w (levelEpsilon l))\n"
                      "        (positiveBankTest η w (ρ*levelEpsilon l/c)) (2 * κ l) := by\n"
                      "  intros; exact ⟨rfl, rfl⟩", source)
        # The estimator has no argument for the true law.
        self.assertIn(f"    {ESTIMATOR} =\n"
                      "      plannedEstimator r (fun i => incrementCall "
                      "(robustFamily η (referenceWeights σ)\n"
                      "        (referenceWeights_probability σ ht hs hN) hc hρc κ) i.val) := by\n"
                      "  intros; rfl", source)
        self.assertIn("(hc : 0 < c) (hρc : ρ ≤ c) (l L : ℕ) (ω : ℕ → Bool),\n"
                      "    0 < raceCost (negativeBankTest weights (levelEpsilon l))\n"
                      "      (positiveBankTest η weights (ρ*levelEpsilon l/c)) L ω", source)

    def test_level_statements_are_under_the_true_law(self):
        source, _ = audit.audit_input()
        # The true law is the second marginal of an increasing coupling with
        # first marginal c eta, plus the uncoupled part.
        self.assertEqual(source.count(TRUE_LAW), 10)
        self.assertIn("(hκ : eta ν (4 ^ κ l) ≤ levelAccuracy ρ l/8) "
                      "(hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8),\n"
                      "    |(∫ ω, (robustFamily η w hw hc hρc κ l).value ω "
                      "∂originalPopulationTapeLaw μ q)-\n"
                      "      signMean μ q.val| ≤ levelAccuracy ρ l", source)
        self.assertIn("(hκ : ∀ j, j ≤ l → eta ν (4 ^ κ j) ≤ levelAccuracy ρ j/8) "
                      "(hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8),\n"
                      "    (∫ ω, ((incrementCall (robustFamily η w hw hc hρc κ) l).value ω)^2\n"
                      "      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ l", source)
        # Work and price: the uncoupled mass is added to the unresolved mass.
        self.assertIn("      planLevelWork τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))\n"
                      "      (ζ.real univ + μ₀.real univ) l (κ l) := @robustFamily_work", source)
        self.assertIn("      planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))\n"
                      "      (ζ.real univ + μ₀.real univ) l (κ l) := @robustFamily_price", source)

    def test_plan_validity_is_restated_in_full(self):
        source, _ = audit.audit_input()
        self.assertIn("(hC : ∀ l, planLevelPrice τ ρ (costEntropy (fun j : Fin N => "
                      "bandCost σ j.val)) (ζ.real univ + μ₀.real univ) l (κ l) ≤ C l) "
                      "{J : ℕ} (r : Fin (J+1) → ℝ≥0) "
                      "(hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost C i.val ≤ B),\n"
                      f"    RareBudget μ ({ESTIMATOR}) ρ B", source)
        self.assertEqual(source.count(
            "(hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8) "
            "(hzJ : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ J/8)"), 2)
        self.assertIn("      ENNReal.ofReal (planCertificate ρ r) := @robust_plan_squaredRisk",
                      source)
        # From an enclosure of the reference design that covers the uncoupled mass.
        self.assertIn("(E : SplitEnclosure σ τ ζ N) "
                      "(hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved) (κ : ℕ → ℕ) {J : ℕ} "
                      "(hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8) "
                      "(hzJ : E.unresolved ≤ levelAccuracy ρ J/8)", source)
        self.assertIn(f"    RareBudget μ ({ESTIMATOR}) ρ B ∧\n"
                      f"      rareRisk μ ({ESTIMATOR}) ρ ≤\n"
                      "      ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := "
                      "@robust_enclosed_plan_valid", source)
        self.assertIn("{ρ z : ℝ} (hρ : 0 < ρ) (hz : z ≤ E.unresolved) (l k : ℕ),\n"
                      "    planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) "
                      "z l k ≤\n      E.price ρ l k", source)
        # The planner's own caps and counts.
        self.assertIn("(hvan : EnvelopeVanishes E.resolvedError) {J : ℕ} "
                      "(hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) "
                      "(hw : ∀ i, 0 < w i),", source)
        self.assertIn("      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) "
                      "w))) := @robust_searched_plan_valid", source)

    def test_one_estimator_for_every_true_law(self):
        source, _ = audit.audit_input()
        # The estimator is chosen before the true law, in both statements.
        self.assertEqual(source.count(EVERY_TRUE_LAW), 2)
        self.assertIn("{z₀ ρ B : ℝ} (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),\n"
                      f"{EVERY_TRUE_LAW} := @robust_planner_rate", source)
        # From upper bounds: a tight enclosure of the zero-atom design and
        # weights within a factor two.
        self.assertIn("(E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ)) "
                      "(w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)", source)
        self.assertIn("(hup : ∀ i, w i ≤ 2 * Real.sqrt (17*levelAccuracy ρ i.val / "
                      "planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) "
                      "(planTerminal hρ B E.unresolved) i)),\n"
                      f"{EVERY_TRUE_LAW} := @robust_zero_atom_planner_rate", source)
        self.assertIn("(hμ : μ = π.map Prod.snd + μ₀),\n    μ₀.real univ = z₀", source)
        self.assertIn("1 + 4 * max 4096 (224000 * Real.sqrt 2) = plannedCoefficient 28000",
                      source)

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
