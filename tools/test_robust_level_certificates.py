"""Reject unregistered declarations, proof escapes and unsound reports in the robust-level audit."""
import unittest
from unittest.mock import patch

import verify_robust_level_certificates as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.RobustContinuation."
DESIGN = ("(η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] "
          "[IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) "
          "(hdesign : σ+τ+ζ = ENNReal.ofReal c • η)")
COUPLING = ("(π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)")
LEVEL_BANK = ("(negativeBankTest (referenceWeights σ) (levelEpsilon l))\n"
              "      (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c))")
CERTIFICATE = ("      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +\n"
               "      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +\n"
               "      2*Uniform713.cap L*(ζ.real univ + μ₀.real univ)")


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class RobustLevelAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_coupling_split_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # Any measure, any measurable map: the parts sum to the measure and
        # have the prescribed images.
        self.assertIn("(π : Measure α) {p : α → γ} (hp : Measurable p) (ν₁ ν₂ : Measure γ) "
                      "[IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (h : π.map p = ν₁ + ν₂),\n"
                      "    ∃ π₁ π₂ : Measure α, π₁ + π₂ = π ∧ π₁.map p = ν₁ ∧ π₂.map p = ν₂",
                      source)
        self.assertIn("(h : π.map p = ν₁ + ν₂ + ν₃),\n"
                      "    ∃ π₁ π₂ π₃ : Measure α, π₁ + π₂ + π₃ = π ∧ π₁.map p = ν₁ ∧ "
                      "π₂.map p = ν₂ ∧\n      π₃.map p = ν₃", source)
        self.assertIn("(π.withDensity (g ∘ p)).map p = (π.map p).withDensity g", source)

    def test_scaled_bank_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # The design sums to c eta, the bank's null law is eta, and its
        # positive allowance is rho eps / c.
        self.assertEqual(source.count(DESIGN), 6)
        self.assertIn("{d₀ d : Gap} (hd : d₀ ∈ band j) (h : (d₀:ℝ) ≤ d),\n"
                      "    conditionalRaceWork (negativeBankTest weights ε) "
                      "(positiveBankTest η weights (ρ*ε/c))\n      L true d ≤\n"
                      "      12*positiveAllowance ε (weights j:ℝ) ρ "
                      "(threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2", source)
        # The sign law is read at the true gap, the bound at the reference gap.
        self.assertIn("    mixtureRaceWork q (negativeBankTest weights ε) "
                      "(positiveBankTest η weights (ρ*ε/c)) L d ≤\n"
                      "      12*(d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))+\n"
                      "      12*q.val d*(d₀:ℝ)⁻¹^2*logPlus (threePieceEnvelope σ τ ζ d₀/ρ)",
                      source)
        self.assertIn("threePieceEnvelope (a • σ) (a • τ) (a • ζ) d = "
                      "a.toReal * threePieceEnvelope σ τ ζ d", source)

    def test_parts_of_the_coupling_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # Selected core: reference marginal sigma, positive mass at most rho
        # under the coupling, work read at the true gap.
        self.assertIn(f"{DESIGN} {COUPLING} (hfst : π.map Prod.fst = σ) {{t ε ρ : ℝ}}", source)
        self.assertIn("(hz : ζ.real univ ≤ ρ) (q : SignLaw) (hq : (∫ z, q.val z.2 ∂π) ≤ ρ) "
                      "(l L : ℕ),\n"
                      f"    (∫ z, mixtureRaceWork q {LEVEL_BANK} L z.2 ∂π) ≤\n"
                      "      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +\n"
                      "      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ", source)
        self.assertIn("      12*costEntropy (fun j : Fin N => bandCost σ j.val) +\n"
                      "      12*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)*Real.log (ε⁻¹) +\n"
                      "      12*(Real.log 3+1)*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) +\n"
                      "      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ", source)
        # Resolved tail: any race, an increasing coupling. Unresolved: the cap.
        self.assertIn(f"{COUPLING} (τ : Measure Gap) [IsFiniteMeasure τ] "
                      "(hfst : π.map Prod.fst = τ) (q : SignLaw) (neg pos : PrefixTest) (L : ℕ),\n"
                      "    (∫ z, mixtureRaceWork q neg pos L z.2 ∂π) ≤ "
                      "2*ordinaryCost τ (Uniform713.cap L)", source)
        self.assertIn("    (∫ z, mixtureRaceWork q neg pos L z.2 ∂π) ≤ "
                      "2*Uniform713.cap L*π.real univ", source)
        self.assertIn("(∫ z, f z ∂π) = ∑ j : Fin N, ∫ z in Prod.fst ⁻¹' band j.val, f z ∂π",
                      source)

    def test_level_certificates_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # One coupling with first marginal c eta; the true law is its second
        # marginal plus the uncoupled part, and the prior is rare under it.
        self.assertIn(f"{DESIGN} {COUPLING} (href : π.map Prod.fst = ENNReal.ofReal c • η) "
                      "(μ₀ : Measure Gap) [IsFiniteMeasure μ₀] {t ρ : ℝ} {N : ℕ}", source)
        self.assertIn("(hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (l L : ℕ),\n"
                      f"    (∫ d, mixtureRaceWork q {LEVEL_BANK} L d\n"
                      f"      ∂(π.map Prod.snd + μ₀)) ≤\n{CERTIFICATE} := "
                      "@robust_three_piece_level_work", source)
        # Three couplings; the one of the unresolved part need not be increasing.
        self.assertIn("(hupσ : ∀ᵐ z ∂πσ, (z.1:ℝ) ≤ z.2) (hupτ : ∀ᵐ z ∂πτ, (z.1:ℝ) ≤ z.2) "
                      "(hfσ : πσ.map Prod.fst = σ) (hfτ : πτ.map Prod.fst = τ) "
                      "(hfζ : πζ.map Prod.fst = ζ)", source)
        self.assertNotIn("hupζ", source)
        self.assertEqual(source.count(CERTIFICATE), 2)
        # The error, with the uncoupled mass in the unresolved mass.
        self.assertIn("(hk : eta ν (4 ^ k) ≤ levelAccuracy ρ l/8) "
                      "(hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8),\n"
                      "    racePopulationError (π.map Prod.snd + μ₀) q "
                      "(negativeBankTest weights (levelEpsilon l))\n"
                      "      (positiveBankTest η weights (ρ*levelEpsilon l/c)) (2*k) ≤ "
                      "levelAccuracy ρ l", source)

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
