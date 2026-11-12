"""Reject unregistered declarations, proof escapes and unsound reports in the learned-oracle audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_learned_oracle as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class LearnedOracleAuditTests(unittest.TestCase):
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
        # The multiplier law, the work bound and the slack of (A13).
        self.assertIn("lightLaw μ = (μ.prod lightMultiplier).map lightGap", source)
        self.assertIn("8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +\n"
                      "        2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / "
                      "(quantileThreshold μ ρ) ^ 2", source)
        self.assertIn("128 * pilotWorkBound μ ρ J + 128 / (pilotCoinCap J ρ : ℝ) + c", source)
        # The witness: the unit mass at zero when e >= 1, else e at zero and the quantile part.
        self.assertIn("if 1 ≤ e then Measure.dirac 0\n"
                      "      else ENNReal.ofReal e • Measure.dirac 0 +\n"
                      "        (128 : ℝ≥0∞) • (quantileTail η ((1 - e) / 128)).map Subtype.val",
                      source)

    def test_statements_carry_their_constants_and_hypotheses(self):
        source, _ = audit.audit_input()
        # The unresolved probabilities against the multiplier law.
        self.assertIn("tailUnresolvedMass μ j ≤ (lightLaw μ).real "
                      "{y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)}", source)
        # (A13): every point, the certificates' hypotheses and the clipped bound.
        self.assertIn("(U : ℕ → ℝ) (hU0 : ∀ i, 0 ≤ U i) (hU1 : U 0 = 1) "
                      "(hbound : ∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)) (x : ℝ),\n"
                      "    envelopeLaw (prefixMinimum U) (J - 1) (Set.Iic x) ≤", source)
        self.assertIn("ENNReal.ofReal (min 1 (128 * (lightLaw μ).real {y : Gap | (y : ℝ) ≤ x} +\n"
                      "      learnedSlack μ ρ J (prefixMinimum U (J - 1))))", source)
        # (A14): the rarity range, the onset, the deepest certificate and 2^22.
        self.assertIn("(hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) "
                      "(hon : PilotOnset μ ρ J) (U : ℕ → ℝ) "
                      "(hbound : U (J - 1) ≤ pilotBound μ J ρ J)", source)
        self.assertIn("(learnedSlack μ ρ J (prefixMinimum U (J - 1))) ≤\n"
                      "      4194304 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        # The strict form of the paper, and the explicit constant behind it.
        self.assertIn("(learnedSlack μ ρ J (prefixMinimum U (J - 1))) <\n"
                      "      4194304 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        self.assertIn("(learnedSlack μ ρ J (prefixMinimum U (J - 1))) ≤\n"
                      "      2621712 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        self.assertEqual(4194304, 2 ** 22)
        self.assertEqual(2621712, 256 * 8193 + 16 + 128 * 4096)
        self.assertIn("ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) ≠ ⊤ ∧\n"
                      "      0 < (ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)).toReal", source)
        # The witness: domination, unit mass, distribution function and support.
        self.assertIn("clippedLaw η e ≤\n      ENNReal.ofReal 128 • η.map Subtype.val + "
                      "ENNReal.ofReal e • Measure.dirac 0", source)
        self.assertIn("IsProbabilityMeasure (clippedLaw η e)", source)
        self.assertIn("{e : ℝ} (he : 0 ≤ e) {x : ℝ} (hx : 0 ≤ x),\n"
                      "    clippedLaw η e (Set.Iic x) =\n"
                      "      ENNReal.ofReal (min 1 (128 * η.real {d : Gap | (d : ℝ) ≤ x} + e))",
                      source)
        self.assertIn("clippedLaw η e (Set.Iio 0) = 0", source)
        self.assertIn("(quantileTail η r).real {d : Gap | (d : ℝ) ≤ x} =\n"
                      "      min r (η.real {d : Gap | (d : ℝ) ≤ x})", source)
        # (A11): the zero-extended selection functional of the learned law and 2^24.
        self.assertIn("(hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) "
                      "(hon : PilotOnset μ ρ J) (U : ℕ → ℝ) (hU0 : ∀ i, 0 ≤ U i) "
                      "(hU1 : U 0 = 1) (hbound : ∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)),\n"
                      "    zeroSelection (envelopeLaw (prefixMinimum U) (J - 1)) ρ (4 ^ J) ≤\n"
                      "      16777216 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        self.assertEqual(16777216, 2 ** 24)
        self.assertEqual(source.count("16777216 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)"),
                         5)
        # The onset depends on the gap law and the rarity only.
        self.assertIn("(hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),\n"
                      "    ∃ J₀ : ℕ, 1 ≤ J₀ ∧ ∀ (J : ℕ) (U : ℕ → ℝ), J₀ ≤ J →", source)
        self.assertIn("∃ J₀ : ℕ, ∀ (q : SignLaw) (S : LearnedStage R) (J m : ℕ) {ε : ℝ}, "
                      "J₀ ≤ J → 0 < m →", source)

    def test_stage_statements_are_on_the_pilot_event(self):
        source, _ = audit.audit_input()
        # The stage's own certificates and learned law, on an observed word.
        self.assertIn("(hbound : ∀ i, i < J → (pilotStage S J m ρ).upper xs i ≤ "
                      "pilotBound μ J ρ (i + 1)),\n"
                      "    zeroSelection ((pilotStage S J m ρ).learnedLaw xs) ρ (4 ^ J) ≤", source)
        # The event: probability 1 - ε on the coin array, domination and the comparison.
        self.assertIn("(hon : PilotOnset μ ρ J) (hm : 0 < m) (hε : 0 < ε) "
                      "(hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m),\n    1 - ε ≤", source)
        self.assertIn("(Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real",
                      source)
        self.assertIn("{ω | (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤\n"
                      "      (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) "
                      "(Set.Iic x)) ∧\n"
                      "      zeroSelection ((pilotStage S J m ρ).learnedLaw "
                      "(pilotStageWord J m ρ ω)) ρ (4 ^ J) ≤", source)
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
