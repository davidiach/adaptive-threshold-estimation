"""Reject unregistered declarations, proof escapes and unsound reports in the zero-quantile audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_zero_quantile as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."
K = "zeroSelection (zeroAtomLaw z η) ρ B"


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class ZeroQuantileAuditTests(unittest.TestCase):
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
        # The law with a zero atom, and the normalization of its positive part.
        self.assertIn("ENNReal.ofReal z • Measure.dirac 0 + "
                      "ENNReal.ofReal (1 - z) • η.map Subtype.val", source)
        self.assertIn("zeroMass α = α.real {0}", source)
        self.assertIn("positiveLaw α = (ENNReal.ofReal (1 - zeroMass α))⁻¹ • positivePart α",
                      source)
        self.assertIn("conditionalRarity ρ z = (ρ - z) / (1 - z)", source)
        # The design value: the constant fallback for z >= ρ, else the cap and three terms.
        self.assertIn("if ρ ≤ z then ENNReal.ofReal ρ\n      else min (ENNReal.ofReal ρ)\n"
                      "        (ENNReal.ofReal z +", source)
        self.assertIn("(tailModulus (quantileTail η (conditionalRarity ρ z)) (budgetScale B)) +",
                      source)
        self.assertIn("(ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *\n"
                      "                measureCostEntropy (quantileCore η (conditionalRarity ρ z))))"
                      " ^ (1 / (2 : ℝ))", source)
        self.assertIn("quantileDesignValue α ρ B = "
                      "zeroQuantileValue (zeroMass α) (positiveLaw α) ρ B", source)

    def test_comparison_carries_its_range_and_constant(self):
        source, _ = audit.audit_input()
        # (A16) for the parametrized law: every z >= 0, rho <= 1/4, B > 0, constant 4.
        self.assertIn("[IsProbabilityMeasure η] {z ρ B : ℝ} (hz0 : 0 ≤ z) (hρ : 0 < ρ) "
                      "(hρ4 : ρ ≤ 1 / 4) (hB : 0 < B),\n"
                      f"    zeroQuantileValue z η ρ B ≤ 4 * {K}", source)
        # (A16) for every probability law on [0, 1/2], with the support hypothesis.
        self.assertIn("(α : Measure ℝ) [IsProbabilityMeasure α] "
                      "(hsupp : α (Set.Icc 0 (1 / 2))ᶜ = 0) {ρ B : ℝ} (hρ : 0 < ρ) "
                      "(hρ4 : ρ ≤ 1 / 4) (hB : 0 < B),\n"
                      "    quantileDesignValue α ρ B ≤ 4 * zeroSelection α ρ B", source)
        # The converse, and the identification with an admissible objective.
        self.assertIn(f"{K} ≤ zeroQuantileValue z η ρ B", source)
        self.assertIn("zeroSelection α ρ B ≤ quantileDesignValue α ρ B", source)
        self.assertIn("zeroObjective (zeroAtomLaw z η) ρ B\n"
                      "      ((ENNReal.ofReal (1 - z) • quantileCore η (conditionalRarity ρ z))"
                      ".map Subtype.val) =", source)
        # The three ingredients of the proof.
        self.assertIn("min (ENNReal.ofReal ρ) (α {0}) ≤ zeroSelection α ρ B", source)
        self.assertIn("(hz1 : z < 1) (hr : 0 ≤ r) (hcr : (1 - z) * r ≤ ρ),\n"
                      "    ENNReal.ofReal (1 - z) * ThresholdHC.EntropyTail.selection η r B ≤ "
                      "zeroSelection (zeroAtomLaw z η) ρ B", source)
        self.assertIn("(hz : 2 * z ≤ ρ),\n    zeroQuantileValue z η ρ B ≤\n"
                      "      ENNReal.ofReal z +\n"
                      "      ENNReal.ofReal (Real.sqrt 2 * (1 - z)) *\n"
                      "      closedQuantileValue η (conditionalRarity ρ z) B", source)
        # Normalization, and agreement with the closed quantile value without a zero atom.
        self.assertIn("(hz : zeroMass α < 1),\n    IsProbabilityMeasure (positiveLaw α) ∧ "
                      "zeroAtomLaw (zeroMass α) (positiveLaw α) = α", source)
        self.assertIn("zeroQuantileValue 0 η ρ B = closedQuantileValue η ρ B", source)

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
