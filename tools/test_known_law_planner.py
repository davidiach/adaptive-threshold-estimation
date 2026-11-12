"""Reject unregistered declarations, proof escapes and unsound reports in the planner audit."""
import unittest
from unittest.mock import patch

import verify_known_law_planner as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.KnownLawPlanner."
PLAN = "planEstimator σ τ ζ ht hs hN hρ hρ1 κ r"


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PlannerAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_price_and_certificate_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # The level price: the constants of the checked level-work theorem, capped by 2 * 4^k.
        self.assertIn("128*(l+1)*Γ + 6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + "
                      "2*ordinaryCost τ (4 ^ k) + 2*z*4 ^ k", source)
        self.assertIn("planLevelPrice τ ρ Γ z l k =\n    min (2 * 4 ^ k) "
                      "(planLevelWork τ ρ Γ z l k)", source)
        self.assertIn("E.price ρ l k = min (2 * 4 ^ k)\n      (128*(l+1)*E.entropy + "
                      "6*E.tailInverse^2/ρ + 2*E.tailWork (4 ^ k) + 2*E.unresolved*4 ^ k)", source)
        # The certificate, the estimator, the counts and the cost of one correction.
        self.assertIn("levelAccuracy ρ J ^ 2 + ∑ i : Fin (J+1), 17*levelAccuracy ρ i.val/(r i:ℝ)",
                      source)
        self.assertIn("plannedEstimator r (fun i => incrementCall (planFamily (σ+τ+ζ) "
                      "(referenceWeights σ)", source)
        self.assertIn("poissonPlanEstimator r (fun i => scaleCall ((r i:ℝ)⁻¹) (D i))", source)
        self.assertIn("planCount B k w i = B * w i / ∑ j, k j * w j", source)
        self.assertIn("planCost E ρ κ J i = adjacentCost (fun l => E.price ρ l (κ l)) i.val",
                      source)
        self.assertIn("planFamily μ w hw hρ hρ1 κ l = scheduledCall μ w hw hρ hρ1 l (2 * κ l)",
                      source)

    def test_enclosure_and_cap_search_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # Every field of the enclosure, with the direction of each bound.
        for field in ("costEntropy (fun j : Fin N => bandCost σ j.val) ≤ entropy",
                      "(∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ≤ tailInverse",
                      "ζ.real univ ≤ unresolved",
                      "∀ M : ℝ, eta (σ+τ) M ≤ resolvedError M",
                      "∀ M : ℝ, ordinaryCost τ M ≤ tailWork M"):
            self.assertIn(field, source)
        self.assertIn("⟨entropy, tailInverse, unresolved, resolvedError, tailWork, "
                      "h1, h2, h3, h4, h5⟩", source)
        # The cap search: termination requirement, least cap, start at 4, carried upwards.
        self.assertIn("EnvelopeVanishes e ↔\n    ∀ ε : ℝ, 0 < ε → ∀ k₀ : ℕ, "
                      "∃ k : ℕ, k₀ ≤ k ∧ e (4 ^ k) ≤ ε", source)
        self.assertIn("searchCap e he ε hε k₀ = Nat.find (he ε hε k₀)", source)
        self.assertIn("(div_pos (levelAccuracy_pos hρ 0) (by norm_num)) 1 ∧", source)
        self.assertIn("(div_pos (levelAccuracy_pos hρ (l+1)) (by norm_num)) "
                      "(searchCaps e he hρ l)", source)
        self.assertIn("{k : ℕ} (hk₀ : k₀ ≤ k) (hk : k < searchCap e he ε hε k₀),\n"
                      "    ε < e (4 ^ k)", source)

    def test_validity_theorems_carry_their_hypotheses(self):
        source, _ = audit.audit_input()
        # Work: every price dominates the level price, and the counts spend at most B.
        self.assertIn("(hC : ∀ l, planLevelPrice τ ρ (costEntropy (fun j : Fin N => "
                      "bandCost σ j.val)) (ζ.real univ) l (κ l) ≤ C l)", source)
        self.assertIn("(hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost C i.val ≤ B),\n"
                      f"    RareBudget (σ+τ+ζ) ({PLAN}) ρ B", source)
        # Error: the caps pass the test, the unresolved mass is covered, the counts are positive.
        self.assertIn("(hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8) "
                      "(hzJ : ζ.real univ ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) "
                      "(hr : ∀ i, 0 < (r i:ℝ)) (q : SignLaw) (hq : RarePrior (σ+τ+ζ) ρ q)", source)
        self.assertIn(f"(populationOutput ({PLAN})) (signMean (σ+τ+ζ) q.val) ≤\n"
                      "      ENNReal.ofReal (planCertificate ρ r)", source)
        # From an enclosure: tests against the enclosure, prices from the enclosure.
        self.assertIn("(hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8) "
                      "(hzJ : E.unresolved ≤ levelAccuracy ρ J/8)", source)
        self.assertIn("adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B),\n"
                      f"    RareBudget (σ+τ+ζ) ({PLAN}) ρ B ∧\n"
                      f"      rareRisk (σ+τ+ζ) ({PLAN}) ρ ≤\n"
                      "      ENNReal.ofReal (Real.sqrt (planCertificate ρ r))", source)
        self.assertIn("rareMinimaxRisk (σ+τ+ζ) ρ B ≤\n"
                      "      ENNReal.ofReal (min (ρ/2) (Real.sqrt (planCertificate ρ r)))", source)
        # The planner's own output: searched caps and counts from positive weights.
        self.assertIn("(hvan : EnvelopeVanishes E.resolvedError) {J : ℕ} "
                      "(hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) "
                      "(hw : ∀ i, 0 < w i)", source)
        self.assertIn("(planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)",
                      source)
        # Rounded weights cost at most a factor theta in the variance term.
        self.assertIn("(hlow : ∀ i, sqrt (v i / k i) ≤ w i) (hup : ∀ i, w i ≤ θ * "
                      "sqrt (v i / k i)),\n    ∑ i, v i / planCount B k w i ≤ "
                      "θ * (allocationCertificate v k) ^ 2 / B", source)
        self.assertIn("∑ i, k i * planCount B k w i = B", source)
        # The level certificates at the plan's caps.
        self.assertIn("(∫ ω, ((incrementCall (planFamily μ w hw hρ hρ1 κ) l).value ω)^2\n"
                      "      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ l", source)
        self.assertIn("((planFamily μ w hw hρ hρ1 κ l).cost ω:ℝ) ≤ 2 * 4 ^ κ l", source)

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
