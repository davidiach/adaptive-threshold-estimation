"""Guard the CDF bridge's hypotheses, quantifiers, and complete axiom audit."""

import subprocess
import unittest
from unittest.mock import patch

import verify_blind_upper_components as shared
import verify_robust_cdf_bridge as audit


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class RobustCDFBridgeAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), 12)
        self.assertEqual(roots, {"ThresholdHC.RobustContinuation." + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), 12)
        self.assertEqual(source.count("#print axioms "), 12)
        shared.validate_reports(report(roots), 0, roots)

    def test_cdf_direction_and_zero_mass_are_preserved(self):
        source, _ = audit.audit_input()
        self.assertIn("cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x", source)
        self.assertIn("      (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) ∧\n"
                      "      π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η ∧\n"
                      "      μ = π.map Prod.snd + μ₀ ∧ μ₀.real univ = z₀ := "
                      "@exists_robust_coupling_of_cdf", source)
        self.assertIn("(hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1)", source)

    def test_sign_mass_includes_the_zero_atom_remainder(self):
        source, _ = audit.audit_input()
        self.assertIn("(∫ z, q.val z.2 ∂π) + (∫ d, q.val d ∂μ₀) = signMean μ q.val := "
                      "@coupling_sign_mass", source)
        self.assertIn("(q : SignLaw) {ρ : ℝ} (hq : RarePrior μ ρ q),\n"
                      "    (∫ z, q.val z.2 ∂π) ≤ ρ := @coupling_sign_budget", source)

    def test_plan_certificates_have_no_coupling_input(self):
        source, _ = audit.audit_input()
        statements = source.split("example ")
        for name in ("cdf_robust_enclosed_plan_valid", "cdf_robust_searched_plan_valid"):
            statement = next(s for s in statements if ":= @" + name in s)
            self.assertNotIn("π", statement)
            self.assertNotIn("μ₀", statement)
            self.assertIn("(hE₀ : ζ.real univ + z₀ ≤ E.unresolved)", statement)
            self.assertIn("robustPlanEstimator η σ ht hs hN hc hρc", statement)
            self.assertIn("RareBudget μ", statement)
            self.assertIn("rareRisk μ", statement)

    def test_one_estimator_precedes_every_true_law(self):
        source, _ = audit.audit_input()
        statement = next(s for s in source.split("example ") if ":= @cdf_robust_planner_rate" in s)
        self.assertIn("    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),\n"
                      "      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],\n"
                      "        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →", statement)
        self.assertIn("plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B", statement)
        self.assertNotIn("π", statement)
        self.assertNotIn("μ₀", statement)

    def test_registration_and_unreadable_declarations_fail_closed(self):
        for names in (audit.NAMES + ["hidden"], audit.NAMES[1:]):
            with patch.object(audit, "declared_names", return_value=names):
                with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                    audit.audit_input()
        for declaration in ("private theorem hidden : True := by trivial",
                            "protected def hidden : Nat := 0"):
            with self.subTest(declaration=declaration):
                with patch.object(audit, "strip_comments", side_effect=
                                  lambda source: source + "\n" + declaration + "\n"):
                    with self.assertRaisesRegex(ValueError, "registry cannot read"):
                        audit.declared_names()

    def test_restatements_are_bound_to_the_registered_declarations(self):
        with patch.object(audit, "bind_restatements", wraps=shared.bind_restatements) as bind:
            source, _ = audit.audit_input()
            bind.assert_called_once()
        altered = source.replace("@cdf_robust_planner_rate", "@cdf_robust_searched_plan_valid")
        with self.assertRaisesRegex(ValueError, "No restated statement names cdf_robust_planner_rate"):
            shared.bind_restatements(altered, audit.NAMES)

    def test_proof_escape_is_rejected(self):
        with patch.object(audit, "strip_comments", side_effect=
                          lambda source: source + "\ntheorem hidden : False := by sorry\n"):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.declared_names()

    def test_main_rejects_missing_unsound_and_failed_reports(self):
        _, roots = audit.audit_input()
        bad_reports = [(report(sorted(roots)[1:]), 0), (report(roots, "sorryAx"), 0),
                       (report(roots), 1)]
        for output, returncode in bad_reports:
            with self.subTest(returncode=returncode, output=output[:80]):
                with patch.object(audit.subprocess, "run", side_effect=[
                    subprocess.CompletedProcess([], 0),
                    subprocess.CompletedProcess([], returncode, stdout=output, stderr=""),
                ]), patch("builtins.print"):
                    with self.assertRaises(ValueError):
                        audit.main()


if __name__ == "__main__":
    unittest.main()
