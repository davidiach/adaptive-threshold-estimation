"""Reject unregistered declarations, proof escapes and unsound reports in the planner-estimator audit."""
import unittest
from unittest.mock import patch

import verify_known_law_planner_estimator as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.KnownLawPlanner."
K = "ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B"


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PlannerEstimatorAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_the_estimators_are_named_in_both_branches(self):
        source, _ = audit.audit_input()
        # The plan's estimator is the plan of the enclosure, at its searched caps.
        self.assertIn("quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w =\n"
                      "      planEstimator σ τ ζ ht hs hN hρ hρ4 (searchCaps E.resolvedError hvan hρ)",
                      source)
        # The decision compares the plan's certified risk with the constant's.
        self.assertIn("RunsPlan E hρ hvan B w ↔\n"
                      "      2048 * E.unresolved ≤ ρ ∧ sqrt (planCertificate ρ", source)
        # Both branches bound the returned estimator's budget and risk, not the
        # minimax risk.
        self.assertNotIn("rareMinimaxRisk", source)
        self.assertEqual(source.count("RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧"), 3)
        self.assertIn(f"rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤ ENNReal.ofReal 44801 * {K}",
                      source)
        self.assertIn("rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN "
                      "(SplitEnclosure.exact σ τ ζ N) (eta_vanishes (σ+τ)) B "
                      f"(exactWeights σ τ ζ hρ B N)) ρ ≤ ENNReal.ofReal 44801 * {K}", source)
        self.assertIn("rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hE.vanishes "
                      "B w) ρ ≤ ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ))", source)
        # The exact weights are the optimal ones.
        self.assertIn("exactWeights σ τ ζ hρ B N i =\n      sqrt (17*levelAccuracy ρ i.val /", source)

    def test_unregistered_declaration_rejected(self):
        with patch.object(audit, "declared_names", return_value=audit.NAMES + ["extra_lemma"]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()
        with patch.object(audit, "declared_names", return_value=audit.NAMES[1:]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()

    def test_unreadable_declaration_rejected(self):
        hidden = lambda source: source + "\nprivate theorem hidden : True := trivial\n"
        with patch.object(audit, "strip_comments", side_effect=hidden):
            with self.assertRaisesRegex(ValueError, "registry cannot read"):
                audit.declared_names()

    def test_proof_escape_rejected(self):
        for text in ("\ntheorem hidden : False := by sorry\n",
                     "\nexample : 2 + 2 = 4 := by decide (native := true)\n",
                     "\nscoped instance hijack : LE ℝ := ⟨fun _ _ => True⟩\n"):
            with self.subTest(text=text.strip()):
                with patch.object(audit, "strip_comments", side_effect=lambda s, t=text: s + t):
                    with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                        audit.declared_names()

    def test_missing_or_unsound_report_rejected(self):
        _, roots = audit.audit_input()
        with self.assertRaises(ValueError):
            shared.validate_reports(report(sorted(roots)[1:]), 0, roots)
        with self.assertRaises(ValueError):
            shared.validate_reports(report(roots, "propext, sorryAx"), 0, roots)
        with self.assertRaises(ValueError):
            shared.validate_reports(report(roots), 1, roots)


if __name__ == "__main__":
    unittest.main()
