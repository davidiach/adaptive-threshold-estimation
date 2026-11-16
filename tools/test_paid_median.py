"""Regression guards for the conditional capped-median and paid-stage audit."""

import subprocess
import unittest
from unittest.mock import patch

import verify_blind_upper_components as shared
import verify_paid_median as audit


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PaidMedianAuditTests(unittest.TestCase):
    def setUp(self):
        self.source, self.roots = audit.audit_input()

    def statement(self, name):
        return next(s for s in self.source.split("example ") if ":= @" + name + "\n" in s)

    def test_complete_registration_and_reports(self):
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), 48)
        self.assertEqual(self.source.count("example "), 48)
        self.assertEqual(self.source.count("#print axioms "), 48)
        self.assertEqual(self.roots, {"ThresholdHC.RobustContinuation." + n for n in audit.NAMES})
        shared.validate_reports(report(self.roots), 0, self.roots)

    def test_reference_estimator_is_fixed_before_the_true_law(self):
        s = self.statement("reference_base_exists")
        self.assertLess(s.index("∃ (R : Type)"), s.index("∀ (μ : Measure Gap)"))
        self.assertIn("cdf (μ.map Subtype.val) x ≤ cdf α x", s)
        self.assertIn("RareBudget μ A ρ b", s)
        self.assertIn("rareRisk μ A ρ ≤ ENNReal.ofReal (referenceRadius α ρ b)", s)
        # The exact reference validity predicate has no small-zero-atom assumption.
        validity = self.source.split("example ")[1]
        self.assertIn("IsProbabilityMeasure α ∧ α (Set.Icc 0 (1/2))ᶜ = 0", validity)
        self.assertNotIn("zeroMass", validity)

    def test_seed_and_word_construction_are_checked(self):
        self.assertIn("(∀ α : Measure ℝ, ℕ → ReferenceSeed α ρ (medianBaseBudget B m))", self.source)
        self.assertIn("(medianStage ρ B m).continuationCost = (2*m+1) * medianCopyCap B m", self.source)
        self.assertIn(".getD (M/2)", self.source)
        self.assertIn("medianStage_seed_law", self.source)
        self.assertIn("medianStage_fixed_interval_law", self.source)

    def test_conditional_guarantee_is_for_actual_paid_prefix(self):
        s = self.statement("paidMedianStage_conditional_coverage")
        self.assertIn("(hxs : (experimentLaw", s)
        self.assertIn(".pilotCost = xs} ≠ 0)", s)
        self.assertIn("(processHistory z.2 S.cap).take S.pilotCost", s)
        self.assertIn("(S.endpoint false).output (z.1.1,z.2)", s)
        self.assertIn("(intervalFailure (signMean μ q.val))", s)
        self.assertIn("(hq : RarePrior μ ρ q)", s)
        self.assertNotIn("(hw", s)
        self.assertNotIn("(hR", s)
        self.assertNotIn("rareRisk", s)
        self.assertNotIn("∀ d, q.val d ≤ ρ", s)

    def test_null_histories_are_handled_without_normalizing(self):
        s = self.statement("original_restrict_interval_law")
        self.assertNotIn("(hxs", s)
        self.assertNotIn("⁻¹", s)
        self.assertIn(".restrict", s)

    def test_cap_and_radius_do_not_assume_a_good_pilot(self):
        cap = self.statement("paidMedianStage_cap")
        self.assertIn("(upper : Bool)", cap)
        self.assertIn("(k * pilotSpan J + ⌊B⌋₊)", cap)
        self.assertNotIn("hdom", cap)
        self.assertNotIn("RarePrior", cap)
        radius = self.statement("paidMedianStage_reported_radius")
        self.assertIn("(w : List Bool)", radius)
        self.assertNotIn("hdom", radius)
        self.assertIn("2 * medianRadius (S.learnedLaw (w.take S.pilotCost))", radius)
        self.assertIn("6 * plannedCoefficient 28000", self.statement("medianRadius_le"))

    def test_full_stage_has_pilot_plus_continuation_error(self):
        s = self.statement("paidMedianStage_at_level")
        self.assertIn("8 * Real.log (2 * (J : ℝ) / ε) ≤ k", s)
        self.assertIn("paidMedianStage ρ B (groups δ) J k", s)
        self.assertIn("PathwiseCap (S.endpoint false)", s)
        self.assertIn("≤ ENNReal.ofReal (ε + δ)", s)
        self.assertNotIn("hdom", s)
        self.assertNotIn("rareRisk", s)

    def test_unregistered_and_unsupported_declarations_fail_closed(self):
        with patch.object(audit, "NAMES", audit.NAMES[:-1]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()
        with patch.object(audit, "strip_comments", side_effect=
                          lambda s: s + "\nprivate theorem hidden : True := trivial\n"):
            with self.assertRaisesRegex(ValueError, "registry cannot read"):
                audit.declared_names()

    def test_proof_escape_and_substituted_restatement_fail_closed(self):
        with patch.object(audit, "strip_comments", side_effect=
                          lambda s: s + "\ntheorem hidden : False := by sorry\n"):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.declared_names()
        with self.assertRaisesRegex(ValueError, "No restated statement names paidMedianStage_at_level"):
            shared.bind_restatements(self.source.replace("@paidMedianStage_at_level", "@paidMedianStage_coverage"), audit.NAMES)

    def test_main_rejects_incomplete_unsound_or_failed_report(self):
        for output, code in [(report(sorted(self.roots)[1:]), 0), (report(self.roots, "sorryAx"), 0),
                             (report(self.roots), 1)]:
            with self.subTest(code=code, output=output[:60]):
                with patch.object(audit.subprocess, "run", side_effect=[
                    subprocess.CompletedProcess([], 0),
                    subprocess.CompletedProcess([], code, stdout=output, stderr=""),
                ]), patch("builtins.print"):
                    with self.assertRaises(ValueError):
                        audit.main()


if __name__ == "__main__":
    unittest.main()
