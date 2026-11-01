"""Fail-closed checks for the supporting lower-bound audit and its scope."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_entropy_tail_lower_components as audit


class LowerComponentAuditTests(unittest.TestCase):
    def test_registry_and_dependency_order(self):
        paths, ordered, roots = audit.validate_sources()
        self.assertEqual(len(paths), 29)
        self.assertEqual(len(roots), 189)
        self.assertTrue(set(audit.EXACT_TARGETS) <= roots)
        self.assertEqual([p for p in ordered if p in paths], paths)

    def test_success_does_not_claim_the_full_lower_bound(self):
        status = audit.scope_status(True)
        self.assertTrue(status["valid"])
        self.assertTrue(status["weighted_sign_entropy_verified"])
        self.assertTrue(status["certificate_lower_reduction_verified"])
        self.assertTrue(status["fair_gate_probability_verified"])
        self.assertTrue(status["biased_gate_transfer_verified"])
        self.assertTrue(status["fixed_repeat_gate_bounds_verified"])
        self.assertTrue(status["population_gate_moment_work_verified"])
        self.assertTrue(status["early_output_decomposition_verified"])
        self.assertTrue(status["signwise_gate_likelihood_difference_verified"])
        self.assertTrue(status["integrated_early_output_bound_verified"])
        self.assertTrue(status["small_work_activation_positive_verified"])
        self.assertTrue(status["gated_good_gaps_verified"])
        self.assertTrue(status["gated_moment_floor_verified"])
        self.assertTrue(status["gated_annular_saturation_verified"])
        self.assertTrue(status["certificate_centering_verified"])
        self.assertTrue(status["certificate_one_coin_verified"])
        self.assertTrue(status["large_bias_certificate_lower_verified"])
        self.assertTrue(status["population_embedding_transfer_verified"])
        self.assertTrue(status["certificate_annular_obstruction_verified"])
        for flag in ("full_information_gate_verified", "gate_restart_renewal_verified",
                     "entropy_tail_lower_verified", "entropy_tail_law_verified",
                     "closed_quantile_minimax_verified"):
            self.assertIs(status[flag], False)

    def test_changed_frozen_target_is_rejected(self):
        original = audit.sha
        target = audit.SOURCE / "Specification.lean"
        with patch.object(audit, "sha", side_effect=lambda p: "0" * 64 if p == target else original(p)):
            with self.assertRaisesRegex(ValueError, "Frozen weighted-sign"):
                audit.validate_sources()

    def test_changed_frozen_dependency_is_rejected(self):
        original = Path.read_text
        target = audit.LEAN / "ThresholdHC/CriticalAllSizes/SingleGap.lean"

        def altered(path, *args, **kwargs):
            source = original(path, *args, **kwargs)
            return source + "\nimport ThresholdHC.CriticalEntropy.CriticalAnnuli\n" if path == target else source

        with patch.object(Path, "read_text", altered):
            with self.assertRaisesRegex(ValueError, "Frozen specification dependency"):
                audit.validate_sources()

    def test_missing_exact_target_is_rejected(self):
        with patch.object(audit, "EXACT_TARGETS", {audit.PREFIX + "missing": "False"}):
            with self.assertRaisesRegex(ValueError, "missing declaration"):
                audit.validate_sources()

    def test_unregistered_module_is_rejected(self):
        with patch.object(audit, "MODULES", audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, "unregistered"):
                audit.validate_sources()

    def test_proof_escapes_are_rejected(self):
        original = Path.read_text
        for target in (audit.SOURCE / "WeightedSign.lean",
                       audit.LEAN / "ThresholdHC/CriticalEntropy/FiniteGap.lean"):
            for escape in ("example : False := by sorry", "axiom escape : False",
                           "example : False := by admit", "#guard_msgs in\nexample : False := by sorry",
                           "example : True := by decide +native"):
                with self.subTest(target=target, escape=escape):
                    def altered(path, *args, **kwargs):
                        source = original(path, *args, **kwargs)
                        return source + "\n" + escape if path == target else source
                    with patch.object(Path, "read_text", altered):
                        with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                            audit.validate_sources()

    def test_missing_or_unsafe_axiom_reports_are_rejected(self):
        root = audit.PREFIX + "weighted_sign_entropy"
        for report in ("", f"'{root}' depends on axioms: [sorryAx]",
                       f"'{root}' depends on axioms: [Lean.ofReduceBool]"):
            with self.subTest(report=report):
                with self.assertRaises(ValueError):
                    audit.validate_reports(report, 0, {root})

    def test_failed_lean_exit_is_rejected_even_with_valid_report(self):
        root = audit.PREFIX + "weighted_sign_entropy"
        with self.assertRaisesRegex(ValueError, "unsuccessfully"):
            audit.validate_reports(f"'{root}' depends on axioms: [propext, Classical.choice, Quot.sound]",
                                   1, {root})


if __name__ == "__main__":
    unittest.main()
