"""Reject unregistered declarations, proof escapes and unsound reports in the robust-work audit."""
import unittest
from unittest.mock import patch

import verify_robust_coin_work as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.RobustContinuation."
LARGER = "{d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d)"


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class RobustWorkAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_ordinary_work_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # The kernel decreases with the gap, for every positive cap.
        self.assertIn("{M : ℝ} (hM : 0 < M) {d d' : Gap} (h : (d:ℝ) ≤ d'),\n"
                      "    ordinaryWorkKernel M (d':ℝ) ≤ ordinaryWorkKernel M (d:ℝ)", source)
        # Any race, either sign, the kernel at the reference gap.
        self.assertIn("(neg pos : PrefixTest) (L : ℕ) (s : Bool) {d₀ d : Gap} (h : (d₀:ℝ) ≤ d),\n"
                      "    (∫ ω, (raceCost neg pos L ω : ℝ) ∂tapeMeasure (gapParameter s d)) ≤\n"
                      "      2*ordinaryWorkKernel (cap L) (d₀:ℝ)", source)

    def test_negative_bank_work_is_restated_in_full(self):
        source, _ = audit.audit_input()
        self.assertIn("(hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (h : d ≤ d'),\n"
                      "    negativeReferenceDrift d r ≤ negativeReferenceDrift d' r", source)
        # The reference is matched to d0; the coin is a negative coin of gap d.
        self.assertIn("(hdr : (d₀:ℝ)/2 ≤ r) (hrd : r ≤ (d₀:ℝ)) (hb : 0 ≤ b) (M : ℕ),\n"
                      "    (∫ ω, (scoreStop (negativeBitScore r) b M ω : ℝ) "
                      "∂tapeMeasure (gapParameter false d)) ≤\n"
                      "      (3/(4*(d₀:ℝ)^2))*(1+b)", source)
        self.assertIn(f"(hw1 : (weights j:ℝ) ≤ 1) {LARGER},\n"
                      "    (∫ ω, (raceCost (negativeBankTest weights ε) "
                      "(positiveBankTest μ weights u) L ω : ℝ)\n"
                      "      ∂tapeMeasure (gapParameter false d)) ≤\n"
                      "      (3/(2*(d₀:ℝ)^2))*(1+log (ε*(weights j:ℝ))⁻¹)", source)

    def test_positive_bank_work_is_restated_in_full(self):
        source, _ = audit.audit_input()
        self.assertIn("(n : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω'),\n"
                      "    prefixMean observations n ω ≤ prefixMean observations n ω'", source)
        # Survival: every hypothesis is at the reference gap, the coin has gap d.
        self.assertIn(f"{LARGER} {{n : ℕ}} (hn : 0 < n) (hU : U ≤ n*(d₀:ℝ)^2/3) "
                      "(hLap : nullLaplace μ n ≤ V) (hV : V ≤ u*(weights j:ℝ)*exp U),\n"
                      "    (tapeMeasure (gapParameter true d)).real", source)
        self.assertIn("      exp (-(n:ℝ)*(d₀:ℝ)^2/2)", source)
        self.assertIn(f"{LARGER} (hLap : ∀ n : ℕ, 1 ≤ n*(d₀:ℝ)^2 → nullLaplace μ n ≤ V) "
                      "(hV : V ≤ u*(weights j:ℝ)*exp U),", source)
        self.assertIn("      ∂tapeMeasure (gapParameter true d)) ≤ 6*U/(d₀:ℝ)^2", source)
        # The work with the three-piece surcharge at the reference gap.
        self.assertIn("(positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L ω : ℝ)\n"
                      "      ∂tapeMeasure (gapParameter true d)) ≤\n"
                      "      12*positiveAllowance ε (weights j:ℝ) ρ "
                      "(threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2", source)

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
