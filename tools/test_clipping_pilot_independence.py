"""Regression guards for the clipping and conditional production-law audit."""

import subprocess
import unittest
from unittest.mock import patch

import verify_blind_upper_components as shared
import verify_clipping_pilot_independence as audit


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class ClippingPilotAuditTests(unittest.TestCase):
    def test_complete_registration_and_reports(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), 26)
        self.assertEqual(source.count("example "), 26)
        self.assertEqual(source.count("#print axioms "), 26)
        self.assertEqual(roots, {"ThresholdHC.RobustContinuation." + n for n in audit.NAMES})
        shared.validate_reports(report(roots), 0, roots)

    def test_clipping_definition_and_original_experiment_are_checked(self):
        source, _ = audit.audit_input()
        self.assertIn("clippedEstimator A M =\n"
                      "      { A with output := fun z => clipEstimate M (A.output z)", source)
        self.assertIn("experimentLaw μ (clippedEstimator A M) q = experimentLaw μ A q", source)
        self.assertIn("expectedWork μ (clippedEstimator A M) q = expectedWork μ A q", source)
        self.assertIn("PathwiseCap (clippedEstimator A M) n ↔ PathwiseCap A n", source)

    def test_risk_requires_target_in_interval_and_preserves_global_rarity(self):
        source, _ = audit.audit_input()
        self.assertIn("(hθ : 0 ≤ θ ∧ θ ≤ M)", source)
        self.assertIn("rareRisk μ (clippedEstimator A ρ) ρ ≤ rareRisk μ A ρ", source)
        self.assertNotIn("∀ d, q.val d ≤ ρ", source)

    def test_bounded_estimator_precedes_every_true_law(self):
        source, _ = audit.audit_input()
        statement = next(s for s in source.split("example ") if ":= @clipped_cdf_planner_rate" in s)
        self.assertIn("    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),\n"
                      "      (∀ z, 0 ≤ A.output z ∧ A.output z ≤ ρ) ∧\n"
                      "      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],", statement)
        self.assertIn("cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x", statement)

    def test_joint_law_contains_seed_and_distinct_complete_streams(self):
        source, _ = audit.audit_input()
        statement = next(s for s in source.split("example ") if ":= @pilot_production_joint_law" in s)
        self.assertIn("(readBlock n p (z.2 ∘ Nat.pair 0)).1, (z.1, z.2 ∘ Nat.pair 1)", statement)
        self.assertIn(".prod (originalSimulationLaw μ A q)", statement)
        self.assertNotIn("IndepFun", statement)

    def test_null_histories_and_positive_probability_condition_are_distinguished(self):
        source, _ = audit.audit_input()
        statements = source.split("example ")
        restriction = next(s for s in statements if ":= @pilot_restrict_production_law" in s)
        conditional = next(s for s in statements if ":= @pilot_conditional_production_law" in s)
        self.assertNotIn("(hxs", restriction)
        self.assertIn("(hxs :", conditional)
        self.assertIn("= xs} ≠ 0)", conditional)
        self.assertIn("= xs})⁻¹ •", conditional)
        self.assertIn("= originalSimulationLaw μ A q :=", conditional)

    def test_actual_pilot_and_original_experiment_are_connected(self):
        source, _ = audit.audit_input()
        self.assertIn("pilotStageWord J m ρ z.2", source)
        self.assertIn("(processHistory z.2 S.cap).take S.pilotCost", source)
        statement = next(s for s in source.split("example ")
                         if ":= @learnedStage_conditional_interval_law" in s).split("#print axioms")[0]
        self.assertIn("S.interval (S.learnedLaw xs) z.1", statement)
        self.assertIn("S.continuation (S.learnedLaw xs) z.1", statement)
        self.assertNotIn("RareBudget", statement)
        self.assertNotIn("rareRisk", statement)

    def test_selected_seed_space_and_law_can_depend_on_history(self):
        source, _ = audit.audit_input()
        statement = next(s for s in source.split("example ") if ":= @pilot_selected_seed_law" in s)
        self.assertIn("{R : List Bool → Type}", statement)
        self.assertIn("(P : ∀ xs, Measure (R xs))", statement)
        self.assertIn("(fun z => (z.1 xs, z.2 ∘ Nat.pair 1))", statement)
        self.assertIn("(P xs).prod", statement)

    def test_registration_and_unreadable_declarations_fail_closed(self):
        for names in (audit.NAMES + ["hidden"], audit.NAMES[1:]):
            with patch.object(audit, "declared_names", return_value=names):
                with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                    audit.audit_input()
        with patch.object(audit, "strip_comments", side_effect=
                          lambda source: source + "\nprivate theorem hidden : True := by trivial\n"):
            with self.assertRaisesRegex(ValueError, "registry cannot read"):
                audit.declared_names()

    def test_proof_escape_and_substituted_restatement_fail_closed(self):
        with patch.object(audit, "strip_comments", side_effect=
                          lambda source: source + "\ntheorem hidden : False := by sorry\n"):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.declared_names()
        with patch.object(audit, "bind_restatements", wraps=shared.bind_restatements) as bind:
            source, _ = audit.audit_input()
            bind.assert_called_once()
        with self.assertRaisesRegex(ValueError, "No restated statement names pilot_conditional_production_law"):
            shared.bind_restatements(source.replace("@pilot_conditional_production_law",
                                                   "@pilot_history_probability"), audit.NAMES)

    def test_main_rejects_incomplete_unsound_or_failed_report(self):
        _, roots = audit.audit_input()
        for output, code in [(report(sorted(roots)[1:]), 0), (report(roots, "sorryAx"), 0),
                             (report(roots), 1)]:
            with self.subTest(code=code, output=output[:60]):
                with patch.object(audit.subprocess, "run", side_effect=[
                    subprocess.CompletedProcess([], 0),
                    subprocess.CompletedProcess([], code, stdout=output, stderr=""),
                ]), patch("builtins.print"):
                    with self.assertRaises(ValueError):
                        audit.main()


if __name__ == "__main__":
    unittest.main()
