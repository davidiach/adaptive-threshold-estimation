"""Reject unregistered declarations, proof escapes and unsound reports in the robust-error audit."""
import unittest
from unittest.mock import patch

import verify_robust_error_transfer as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.RobustContinuation."
TESTS = "{neg pos : PrefixTest} (hneg : DownwardTest neg) (hpos : UpwardTest pos)"


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class RobustErrorAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_tape_order_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # Flips from common uniforms, and stochastic monotonicity in the coin.
        self.assertIn("{p p' : unitInterval} (h : (p:ℝ) ≤ p') (u : ℕ → ℝ),\n"
                      "    uniformCoinTape p u ≤ uniformCoinTape p' u", source)
        self.assertIn("(hE : MeasurableSet E) (hup : IsUpperSet E),\n"
                      "    tapeMeasure p E ≤ tapeMeasure p' E", source)
        self.assertIn("(hE : MeasurableSet E) (hlow : IsLowerSet E),\n"
                      "    tapeMeasure p' E ≤ tapeMeasure p E", source)
        # Word probabilities on either side of the fair coin.
        self.assertIn("{p : ℝ} (hp : 1/2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {w w' : Fin n → Bool} "
                      "(h : w ≤ w'),\n    streamProb p w ≤ streamProb p w'", source)
        self.assertIn("{p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2) {n : ℕ} {w w' : Fin n → Bool} "
                      "(h : w ≤ w'),\n    streamProb p w' ≤ streamProb p w", source)

    def test_ordinary_classifier_order_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # For every boundary sequence b: no delay, earlier stop is positive, positive stays.
        self.assertIn("(b : ℕ → ℕ → ℝ) {m m' : ℕ → ℝ} (h : ∀ k, m k ≤ m' k) (L : ℕ) "
                      "(hd : firstDecision b m L = 1),\n"
                      "    firstStop b m' L ≤ firstStop b m L", source)
        self.assertIn("(hlt : firstStop b m' L < firstStop b m L),\n"
                      "    firstDecision b m' L = 1", source)
        self.assertIn("(hd : firstDecision b m L = 1),\n    firstDecision b m' L = 1", source)
        # The classifier of the race.
        self.assertIn("(h : ω ≤ ω') (hv : classifierValue L ω = 1),\n"
                      "    classifierStop L ω' ≤ classifierStop L ω", source)
        self.assertIn("(hlt : classifierStop L ω' < classifierStop L ω),\n"
                      "    classifierValue L ω' = 1", source)
        self.assertIn("∀ (L : ℕ),\n    Monotone (classifierValue L)", source)

    def test_race_order_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # The two kinds of test, by definition.
        self.assertIn("DownwardTest t ↔\n"
                      "    ∀ (n : ℕ) (w w' : Fin n → Bool), w ≤ w' → t n w' → t n w := "
                      "fun _ => Iff.rfl", source)
        self.assertIn("UpwardTest t ↔\n"
                      "    ∀ (n : ℕ) (w w' : Fin n → Bool), w ≤ w' → t n w → t n w' := "
                      "fun _ => Iff.rfl", source)
        # The race's output is monotone for every such pair of tests.
        self.assertIn(f"{TESTS} (L : ℕ),\n    Monotone (raceValue neg pos L)", source)
        # The banks: the negative one needs a nonnegative allowance, the
        # positive one holds for every reference law and every allowance.
        self.assertIn("(weights : ℕ → ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε),\n"
                      "    DownwardTest (negativeBankTest weights ε)", source)
        self.assertIn("(μ : Measure Gap) [IsProbabilityMeasure μ] (weights : ℕ → ℝ≥0) (u : ℝ),\n"
                      "    UpwardTest (positiveBankTest μ weights u)", source)
        # The error on one coin, for either sign.
        self.assertIn(f"{TESTS} (L : ℕ) (s : Bool) {{d d' : Gap}} (h : (d:ℝ) ≤ d'),\n"
                      "    raceConditionalError neg pos L s d' ≤ raceConditionalError neg pos L s d",
                      source)

    def test_error_transfer_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # The error at reference gaps with the signs of the true gaps.
        self.assertIn("coupledRaceError π q neg pos L =\n"
                      "      ∫ z, q.val z.2 * raceConditionalError neg pos L true z.1 +\n"
                      "        (1 - q.val z.2) * raceConditionalError neg pos L false z.1 ∂π",
                      source)
        # The transfer: a finite coupling, increasing almost everywhere, plus uncoupled mass.
        self.assertIn(f"{TESTS} (π : Measure (Gap × Gap)) [IsFiniteMeasure π] "
                      "(hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] "
                      "(q : SignLaw) (L : ℕ),\n"
                      "    racePopulationError (π.map Prod.snd + μ₀) q neg pos L ≤\n"
                      "      coupledRaceError π q neg pos L + μ₀.real univ", source)
        # The bank designed from eta: the reference mass is c eta, the prior is rare
        # under the true law, and the bound has the reference law in the integral.
        self.assertIn("{c : ℝ} (hc : 0 ≤ c) (href : π.map Prod.fst = ENNReal.ofReal c • η)", source)
        self.assertIn("(q : SignLaw) (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (L : ℕ),\n"
                      "    racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights ε)\n"
                      "      (positiveBankTest η weights u) L ≤\n"
                      "      ρ*ε + c*u + c*(∫ d : Gap, ordinaryErrorKernel (Uniform713.cap L) "
                      "(d:ℝ) ∂η) +\n      μ₀.real univ", source)

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
