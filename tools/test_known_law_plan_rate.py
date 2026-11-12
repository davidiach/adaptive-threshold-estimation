"""Reject unregistered declarations, proof escapes and unsound reports in the plan-rate audit."""
import unittest
from unittest.mock import patch

import verify_known_law_plan_rate as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.KnownLawPlanner."
K = "ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B"
COEFFICIENT = "1 + 8/5 * max 2048 (28000 * sqrt θ)"


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PlanRateAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_terminal_rule_and_exact_caps_are_restated_in_full(self):
        source, _ = audit.audit_input()
        # The target and the terminal level of the planner.
        self.assertIn("planTarget ρ B z = max (128*z) (ρ/(16*(1+sqrt B)))", source)
        self.assertIn("planTerminal hρ B z = Nat.find (exists_planTerminal hρ B z)", source)
        self.assertIn("∃ l : ℕ, levelAccuracy ρ l/16 < planTarget ρ B z", source)
        self.assertIn("levelAccuracy ρ (planTerminal hρ B z)/16 < planTarget ρ B z", source)
        # Outside the fallback the level is admissible and its accuracy is bounded.
        self.assertIn("{z : ℝ} (hz : 2048*z ≤ ρ),\n"
                      "    z ≤ levelAccuracy ρ (planTerminal hρ B z)/128", source)
        self.assertIn("{z : ℝ} (hz0 : 0 ≤ z),\n"
                      "    levelAccuracy ρ (planTerminal hρ B z) < 2048*z + ρ/(1+sqrt B)", source)
        # Exact envelope: the carried search returns the least admissible caps.
        self.assertIn("searchCaps (eta ν) (eta_vanishes ν) hρ l =\n"
                      "      errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l)",
                      source)
        self.assertIn("levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => "
                      "bandCost σ j.val))", source)

    def test_rate_statements_carry_their_constants_and_hypotheses(self):
        source, _ = audit.audit_input()
        # The multilevel sum of the exact plan, with the coefficient of the upper theorem.
        self.assertIn("28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +\n"
                      "      ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)", source)
        # The certified risk in the design integrals, with weights within a factor theta.
        self.assertIn("levelAccuracy ρ J + sqrt θ * (28000*(sqrt (ρ*costEntropy\n"
                      "      (fun j : Fin N => bandCost σ j.val)) + ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) "
                      "/ sqrt B", source)
        # The floor at a general budget.
        self.assertIn("(hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B),\n"
                      "    ENNReal.ofReal (ρ/(1+sqrt B)) ≤ ThresholdHC.EntropyTail.selection μ ρ B",
                      source)
        # The rate: the split is the quantile split, cut at the budget scale; not the fallback.
        self.assertIn("(hcore : σ = quantileCore (σ+τ+ζ) ρ) "
                      "(htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) "
                      "(hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) "
                      "(hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)", source)
        self.assertIn("(hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) "
                      "(hz : 2048 * ζ.real univ ≤ ρ)", source)
        self.assertIn("ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B", source)
        self.assertEqual(source.count(f"ENNReal.ofReal ({COEFFICIENT}) *\n      {K}"), 2)
        # The fallback: the constant plan obeys the same bound.
        self.assertIn("(hz : ρ < 2048 * ζ.real univ),\n    ENNReal.ofReal (ρ/2) ≤\n"
                      f"      ENNReal.ofReal ({COEFFICIENT}) *", source)
        # The radius: a relative upper square root, six times the coefficient.
        self.assertIn("(hκ : κ * sqrt 8 ≤ 6) (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) c))", source)
        self.assertIn("ENNReal.ofReal r ≤ ENNReal.ofReal (6 * C) * K", source)
        self.assertIn(f"ENNReal.ofReal (6 * ({COEFFICIENT})) *\n      {K}", source)

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
