"""Fail-closed regression tests for the concrete all-budget theorem audit."""

import subprocess
import unittest
from unittest.mock import patch

import verify_blind_upper_components as shared
import verify_arbitrary_law_controller as audit


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class ControllerAuditTests(unittest.TestCase):
    def setUp(self):
        self.source, self.roots = audit.audit_input()

    def statement(self, name):
        return next(s for s in self.source.split("example ") if ":= @" + name + "\n" in s)

    def test_complete_registration_and_reports(self):
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), 99)
        self.assertEqual(self.source.count("example "), 99)
        self.assertEqual(self.source.count("#print axioms "), 99)
        self.assertEqual(self.roots, {"ThresholdHC.ArbitraryLawController." + n for n in audit.NAMES})
        shared.validate_reports(report(self.roots), 0, self.roots)

    def test_exact_pilot_and_observable_controller_are_restatement_targets(self):
        self.assertIn("8 * pilotGroups δ s J + 1", self.source)
        self.assertIn("Nat.findGreatest (fun J => 2 * pilotReservation δ s J ≤ stageCap s) (s + 2)", self.source)
        self.assertIn("if depth δ s = 0 then idleStage S ρ else S", self.source)
        self.assertIn(".pilotCost = 0 ∧", self.source)
        self.assertIn(".continuationCost = 0 ∧", self.source)
        self.assertIn("(fun _ _ _ => (0, ρ))", self.source)
        self.assertIn("processHistory z.2 (spent S k)", self.source)
        self.assertIn("Nat.pair j ∘ (S j).reader (r j)", self.source)

    def test_caps_and_prefixes_are_unconditional(self):
        for name in ("controller_cap", "controller_compatible", "word_prefix", "stage_idle"):
            s = self.statement(name)
            self.assertNotIn("RarePrior", s)
            self.assertNotIn("goodEvent", s)
            self.assertNotIn("PilotOnset", s)
        self.assertIn("PathwiseCap (controller ρ δ B upper) B", self.statement("controller_cap"))
        self.assertIn(".take (spent S k)", self.statement("word_prefix"))

    def test_joint_failure_keeps_the_pilot_for_the_rate(self):
        joint = self.statement("learnedStage_joint_failure_le")
        self.assertIn("¬good", joint)
        self.assertIn("S.tableInterval z.1 z.2 ∈ intervalFailure θ", joint)
        stage = self.statement("stage_failure")
        self.assertIn("(stageBad μ q ρ δ s) ≤", stage)
        self.assertIn("ENNReal.ofReal (stageFailure δ s)", stage)
        self.assertNotIn("(hf", stage)
        self.assertNotIn("(hdom", stage)
        self.assertNotIn("rareRisk", stage)

    def test_budget_constants_and_finite_onset_are_checked(self):
        self.assertIn("B / (4096 * inflation B δ) < (4 : ℝ) ^ depth δ s", self.statement("effective_budget"))
        self.assertIn("(4 : ℝ) ^ depth δ s / 16 ≤", self.statement("continuation_base_ge"))
        self.assertIn("∃ s₀ : ℕ, ∀ s, s₀ ≤ s → J ≤ depth δ s", self.statement("depth_eventually"))
        self.assertIn("∃ H : ℕ, 1 ≤ H ∧ ∀ B : ℕ, H ≤ B", self.statement("completed_depth_eventually"))

    def test_final_theorem_has_no_assumed_stage_or_risk_oracle(self):
        s = self.statement("arbitrary_law_controller")
        self.assertIn("∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∃ H : ℕ", s)
        self.assertLess(s.index("∃ H : ℕ"), s.index("∀ q : SignLaw"))
        self.assertIn("RarePrior μ ρ q →", s)
        self.assertIn("streamLaw μ q ρ δ (successEvent μ q ρ δ H)", s)
        for excluded in ("hcap", "hdom", "rareRisk", "LearnedStage", "(base", "(hf", "∀ d, q.val d ≤ ρ"):
            self.assertNotIn(excluded, s)
        self.assertIn("(∀ B : ℕ", self.source)
        self.assertIn("2 ^ 32 * radiusCoefficient", self.source)
        self.assertIn("radiusCoefficient = 6 * plannedCoefficient 28000", self.source)

    def test_stopping_budget_is_unrestricted_and_uses_same_event(self):
        s = self.statement("successEvent_stopping")
        self.assertIn("hz : z ∈ successEvent μ q ρ δ H", s)
        self.assertIn("τ : (Seed ρ δ × Table) → ℕ", s)
        self.assertIn("H ≤ τ z →", s)
        self.assertNotIn("Measurable τ", s)
        self.assertIn("originalSimulationLaw μ (controller ρ δ B upper) q = streamLaw", self.statement("controller_original_law"))

    def test_unregistered_and_unsupported_declarations_fail_closed(self):
        with patch.object(audit, "NAMES", audit.NAMES[:-1]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()
        with patch.object(audit, "strip_comments", side_effect=lambda s: s + "\nprivate theorem hidden : True := trivial\n"):
            with self.assertRaisesRegex(ValueError, "registry cannot read"):
                audit.declared_names()

    def test_proof_escape_and_missing_final_restatement_fail_closed(self):
        with patch.object(audit, "strip_comments", side_effect=lambda s: s + "\ntheorem hidden : False := by sorry\n"):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.declared_names()
        with self.assertRaisesRegex(ValueError, "No restated statement names arbitrary_law_controller"):
            shared.bind_restatements(self.source.replace("@arbitrary_law_controller", "@controller_cap"), audit.NAMES)

    def test_main_rejects_incomplete_unsound_or_failed_report(self):
        for output, code in [(report(sorted(self.roots)[1:]), 0), (report(self.roots, "sorryAx"), 0), (report(self.roots), 1)]:
            with self.subTest(code=code, output=output[:60]):
                with patch.object(audit.subprocess, "run", side_effect=[
                    subprocess.CompletedProcess([], 0),
                    subprocess.CompletedProcess([], code, stdout=output, stderr=""),
                ]), patch("builtins.print"):
                    with self.assertRaises(ValueError):
                        audit.main()


if __name__ == "__main__":
    unittest.main()
