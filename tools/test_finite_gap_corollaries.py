"""Regression checks for changed targets, omitted roots and proof escapes."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_finite_gap_corollaries as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


def edited(module, change):
    """Patch for Path.read_text that edits one registered module."""
    real_read = Path.read_text

    def read(path, *args, **kwargs):
        text = real_read(path, *args, **kwargs)
        return change(text) if path == audit.SOURCE / f"{module}.lean" else text

    return patch.object(Path, "read_text", read)


class FiniteGapCorollariesAuditTests(unittest.TestCase):
    def test_targets_and_components_are_independently_restated(self):
        source, roots = audit.audit_input()
        for theorem, statement in audit.TARGETS.items():
            self.assertIn("ThresholdHC." + theorem, roots)
            self.assertIn("ThresholdHC." + statement, roots)
            self.assertIn(f"example : {statement} := {theorem}", source)
            self.assertRegex(audit.EXACT, rf":=\s*{theorem}\n")
        for name in audit.COMPONENTS:
            self.assertIn("ThresholdHC." + name, roots)
            self.assertRegex(audit.EXACT, rf":=\s*@?{name}\n")
        self.assertEqual(len(audit.TARGETS), 3)
        self.assertEqual(len(audit.COMPONENTS), 3)
        self.assertEqual(source.count("\nexample"), audit.EXACT_COUNT + len(audit.TARGETS))
        self.assertEqual(source.count("#print axioms "), len(roots))
        for text in ("ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17 * aboveTwoRate (d : ℝ) ρ B) ≤",
                     "ENNReal.ofReal (28000 * aboveTwoRate (d : ℝ) ρ B)",
                     "ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M ≤ (rareMinimaxRisk μ ρ B) ^ 2",
                     "(rareMinimaxRisk μ ρ B) ^ 2 ≤ 2 * 30001 ^ 2 * M",
                     "(∀ d ∈ μ.support, ((d : ℝ) ^ 2)⁻¹ ≤ B) →",
                     "((ENNReal.ofReal J ^ 2 + ENNReal.ofReal ρ * EntropyTailQuantile.measureCostEntropy"):
            self.assertIn(text, audit.EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_every_module_is_imported_and_replayed(self):
        source, _ = audit.audit_input()
        for module in audit.modules():
            self.assertIn(f"import ThresholdHC.{module}\n", source)
        self.assertEqual(audit.replay_modules(), ["ThresholdHC." + m for m in audit.modules()])
        self.assertEqual(len(audit.modules()), 3)

    def test_changed_specification_rejected(self):
        with patch.object(audit, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed finite-gap specification"):
                audit.audit_input()

    def test_hidden_and_missing_modules_rejected(self):
        real_glob = Path.glob

        def extra(path, pattern):
            found = list(real_glob(path, pattern))
            return found + [audit.SOURCE / "Hidden.lean"] if path == audit.SOURCE else found

        with patch.object(Path, "glob", extra):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing FiniteGapCorollaries"):
                audit.audit_input()
        with patch.object(audit, "NAMES", audit.NAMES[:-1]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing FiniteGapCorollaries"):
                audit.audit_input()

    def test_missing_target_rejected(self):
        for module, old in (("Full", "theorem mean_square_form"),
                            ("Corollaries", "theorem closed_quantile_sq"),
                            ("Full", "theorem large_budget_mean_square_form"),
                            ("Corollaries", "theorem tail_linear")):
            with self.subTest(old=old), edited(module, lambda text: text.replace(old, "theorem unrelated")):
                with self.assertRaisesRegex(ValueError, "Missing finite-gap target"):
                    audit.audit_input()

    def test_unrestated_component_rejected(self):
        with patch.object(audit, "COMPONENTS", audit.COMPONENTS + ("FiniteGapCorollaries.min_sq",)):
            with self.assertRaisesRegex(ValueError, "exactly one restated statement"):
                audit.audit_input()
        with patch.object(audit, "EXACT", audit.EXACT.replace(
                "FiniteGapCorollaries.sq_add_le\n", "FiniteGapCorollaries.min_sq\n")):
            with self.assertRaisesRegex(ValueError, "exactly one restated statement"):
                audit.audit_input()

    def test_declaration_outside_its_directory_namespace_rejected(self):
        with edited("Full", lambda text: text.replace(
                "namespace ThresholdHC.FiniteGapCorollaries", "namespace ThresholdHC.PowerWindow").replace(
                "end ThresholdHC.FiniteGapCorollaries", "end ThresholdHC.PowerWindow")):
            with self.assertRaisesRegex(ValueError, "must declare in ThresholdHC.FiniteGapCorollaries"):
                audit.audit_input()

    def test_escapes_and_unreadable_declarations_rejected(self):
        for addition, message in (
            ("\ntheorem bad : False := sorry\n", "Forbidden proof escape"),
            ("\ntheorem bad : 1 = 1 := by native_decide\n", "Forbidden proof escape"),
            ("\ntheorem bad : 1 = 1 := by decide +native\n", "Forbidden proof escape"),
            ("\ninstance : Inhabited Nat := ⟨0⟩\n", "Declaration the registry cannot read"),
            ("\nprotected theorem omitted : True := True.intro\n", "Declaration the registry cannot read"),
            ("\nnamespace Inner\n", "must open exactly one namespace"),
        ):
            for module in ("Corollaries", "Full"):
                with self.subTest(addition=addition, module=module), \
                        edited(module, lambda text: text + addition):
                    with self.assertRaisesRegex(ValueError, message):
                        audit.audit_input()
        with edited("Full", lambda text: "theorem early : True := True.intro\n" + text):
            with self.assertRaisesRegex(ValueError, "Declaration before the namespace"):
                audit.audit_input()

    def test_private_declarations_are_not_roots(self):
        _, roots = audit.audit_input()
        with edited("Full", lambda text: text.replace(
                "\nend ThresholdHC.FiniteGapCorollaries",
                "\nprivate theorem helper : True := True.intro\n\nend ThresholdHC.FiniteGapCorollaries")):
            _, changed = audit.audit_input()
        self.assertEqual(roots, changed)
        self.assertNotIn("ThresholdHC.FiniteGapCorollaries.helper", changed)

    def test_duplicate_declaration_rejected(self):
        with edited("Full", lambda text: text.replace(
                "\nend ThresholdHC.FiniteGapCorollaries",
                "\ntheorem one_gap_rate : True := True.intro\n\nend ThresholdHC.FiniteGapCorollaries")):
            with self.assertRaisesRegex(ValueError, "Duplicate finite-gap declaration"):
                audit.audit_input()

    def test_missing_and_unsound_reports_rejected(self):
        _, roots = audit.audit_input()
        for output, code, message in (
            (report(roots), 1, "exited unsuccessfully"),
            (report(roots - {min(roots)}), 0, "Missing or unexpected"),
            (report(roots, "propext, sorryAx"), 0, "Disallowed transitive axiom"),
            (report(roots, "propext, Lean.ofReduceBool"), 0, "Disallowed transitive axiom"),
            (report(roots) + "warning: declaration uses `sorry`\n", 0, "uses sorry"),
        ):
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    shared.validate_reports(output, code, roots)


if __name__ == "__main__":
    unittest.main()
