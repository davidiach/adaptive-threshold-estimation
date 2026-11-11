"""Reject unregistered declarations, proof escapes and unsound reports in the pilot audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_pilot as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PilotAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_budgets_caps_and_reader_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # (A6): the flip budget of depth j and the completed-coin cap.
        self.assertIn("⌈(4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1))⌉₊ + 2 ^ (J + j - 2)", source)
        self.assertIn("pilotCoinCap J ρ = ⌈Real.sqrt (64 * (4 : ℝ) ^ J / ρ)⌉₊", source)
        self.assertIn("pilotSpan J = ∑ i ∈ Finset.range J, pilotBudget J (i + 1)", source)
        # (A10): both halves, for every target depth at least one.
        self.assertIn("∀ {J : ℕ} (hJ : 1 ≤ J),\n    pilotSpan J ≤ 4 ^ J := @pilotSpan_le", source)
        self.assertIn("∀ {J : ℕ} (hJ : 1 ≤ J),\n    4 ^ J ≤ 2 * pilotSpan J := "
                      "@le_two_mul_pilotSpan", source)
        self.assertIn("pilotCost J m = m * pilotSpan J", source)
        # Block i runs the probes of depth i + 1 with the budget of that depth.
        self.assertIn("seqReader (pilotLength J m) (fun i => medianReader (i + 1) M "
                      "(pilotBudget J (i + 1)) m) J", source)
        self.assertIn("medianWordUpper (i + 1) m (pilotBudget J (i + 1)) M "
                      "(seqWord (pilotLength J m) i w)", source)
        self.assertIn("(fun k c => s (Nat.pair i (Nat.pair k c)))", source)
        # Depth one returns one on every word, not only on reachable ones.
        self.assertIn("∀ (m b M : ℕ) (w : List Bool),\n    medianWordUpper 1 m b M w = 1", source)
        self.assertIn("∀ (J m M : ℕ) (w : List Bool),\n    pilotUpper J m M w 0 = 1", source)
        self.assertIn("(st.count = 1 → st.stopped = true)", source)

    def test_event_and_stage_carry_their_hypotheses(self):
        source, _ = audit.audit_input()
        # (A8): the bound, the event and the common calibration with a finite union.
        self.assertIn("128 * (tailUnresolvedMass μ j + (∫ d : Gap, tailWorkEnvelope j d ∂μ) / "
                      "pilotBudget J j +\n      1 / pilotCoinCap J ρ)", source)
        self.assertIn("(∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤\n"
                      "          medianUpper (i + 1) m b' M' (z i)) ∧", source)
        self.assertIn("(pilotFailure μ J m ρ) ≤ J * (2 * exp (-(m : ℝ) / 8))", source)
        self.assertIn("{ρ ε : ℝ} (hρ : 0 < ρ) (hJ : 1 ≤ J) (hm : 0 < m) (hε : 0 < ε) "
                      "(hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m)", source)
        self.assertIn("(hf : Measurable f) (hlaw : ", source)
        # The pilot alone under the law of the original experiment.
        self.assertIn("(experimentLaw μ (pilotEstimator J m ρ i₀) q).real", source)
        self.assertIn("PathwiseCap (pilotEstimator J m ρ i) (pilotCost J m)", source)
        # The stage: every data field, its labels, its cap and the learned law.
        self.assertIn("(pilotStage S J m ρ).depth = J - 1 ∧", source)
        self.assertIn("(pilotStage S J m ρ).upper = pilotUpper J m (pilotCoinCap J ρ) ∧", source)
        self.assertIn("(pilotStage S J m ρ).continuation = S.continuation ∧", source)
        self.assertIn("stageStreams ω = fun i k c => ω (Nat.pair 0 (Nat.pair i (Nat.pair k c)))",
                      source)
        self.assertIn("PathwiseCap ((pilotStage S J m ρ).endpoint upper)\n"
                      "      (m * pilotSpan J + S.continuationCost)", source)
        self.assertIn("(pilotStage S J m ρ).learnedLaw xs {0} =\n      ENNReal.ofReal "
                      "(prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) (J - 1))", source)
        self.assertIn("Measure.dirac (gridPoint (i.val + 1))", source)
        self.assertIn("(μ.map Subtype.val) (Set.Iic x) ≤ (pilotStage S J m ρ).learnedLaw xs "
                      "(Set.Iic x)", source)
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
