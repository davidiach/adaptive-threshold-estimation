"""Regression checks for changed targets, omitted roots and proof escapes."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_upper_scale as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


def edited(group, module, change):
    """Patch for Path.read_text that edits one registered module."""
    real_read = Path.read_text

    def read(path, *args, **kwargs):
        text = real_read(path, *args, **kwargs)
        return change(text) if path == audit.SOURCES[group] / f"{module}.lean" else text

    return patch.object(Path, "read_text", read)


class UpperScaleAuditTests(unittest.TestCase):
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
        self.assertEqual(len(audit.TARGETS), 2)
        self.assertEqual(len(audit.COMPONENTS), 12)
        self.assertEqual(source.count("\nexample"), audit.EXACT_COUNT + len(audit.TARGETS))
        self.assertEqual(source.count("#print axioms "), len(roots))
        for text in ("minimaxRisk μ B ≤ ENNReal.ofReal (12*modulus μ (1/Real.sqrt B))",
                     "UniformBudget μ (rule B) B ∧",
                     "(399 / 100 : ℝ)",
                     "17 / 4 else 399 / 100)) ≤ 26 / 5",
                     "(26 / 5) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ -",
                     "(21/5)*∫ d, UpperDisagreement.gapRegime L d ∂μ",
                     "BlindUpper.callMark (BlindUpper.paddedMark L) (x, max t 1 * u)",
                     "(4 * (max t 1 * (2 : ℝ) ^ L))",
                     "(169/5) * (∫ d, BlindUpper.callScale L d ∂μ) ^ 2",
                     "ENNReal.ofReal ((1 + (169/5) / t) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2)",
                     "ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B))"):
            self.assertIn(text, audit.EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_every_module_is_imported_and_replayed(self):
        source, _ = audit.audit_input()
        for module in audit.modules():
            self.assertIn(f"import ThresholdHC.{module}\n", source)
        self.assertEqual(audit.replay_modules(), ["ThresholdHC." + m for m in audit.modules()])
        self.assertEqual(len(audit.modules()), 8)

    def test_changed_specification_rejected(self):
        with patch.object(audit, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed upper-scale statement"):
                audit.audit_input()

    def test_hidden_and_missing_modules_rejected(self):
        real_glob = Path.glob
        for group in audit.GROUPS:
            def extra(path, pattern, group=group):
                found = list(real_glob(path, pattern))
                return found + [audit.SOURCES[group] / "Hidden.lean"] if path == audit.SOURCES[group] else found

            with self.subTest(group=group), patch.object(Path, "glob", extra):
                with self.assertRaisesRegex(ValueError, f"Unregistered or missing {group}"):
                    audit.audit_input()
            short = dict(audit.GROUPS)
            short[group] = short[group][:-1]
            with self.subTest(group=group), patch.object(audit, "GROUPS", short):
                with self.assertRaisesRegex(ValueError, f"Unregistered or missing {group}"):
                    audit.audit_input()

    def test_missing_target_rejected(self):
        for group, module, old in (("UpperScale", "Full", "theorem minimax_upper_12"),
                                   ("UpperScale", "Seed", "theorem callMark_scale"),
                                   ("UpperCallCost", "LevelSum", "theorem callCost_constant_le")):
            with self.subTest(old=old), edited(group, module, lambda text: text.replace(old, "theorem unrelated")):
                with self.assertRaisesRegex(ValueError, "Missing upper-scale target"):
                    audit.audit_input()

    def test_unrestated_component_rejected(self):
        with patch.object(audit, "COMPONENTS", audit.COMPONENTS + ("UpperScale.budgetRatio_bounds",)):
            with self.assertRaisesRegex(ValueError, "exactly one restated statement"):
                audit.audit_input()
        with patch.object(audit, "EXACT", audit.EXACT.replace(
                "@UpperScale.scaledBatch_mse\n", "@UpperScale.scaled_squaredRisk_eq\n")):
            with self.assertRaisesRegex(ValueError, "exactly one restated statement"):
                audit.audit_input()

    def test_declaration_outside_its_directory_namespace_rejected(self):
        with edited("UpperCallCost", "Batch", lambda text: text.replace(
                "namespace ThresholdHC.UpperCallCost", "namespace ThresholdHC.UpperScale").replace(
                "end ThresholdHC.UpperCallCost", "end ThresholdHC.UpperScale")):
            with self.assertRaisesRegex(ValueError, "must declare in ThresholdHC.UpperCallCost"):
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
            for group, module in (("UpperCallCost", "Offset"), ("UpperScale", "Seed")):
                with self.subTest(addition=addition, module=module), \
                        edited(group, module, lambda text: text + addition):
                    with self.assertRaisesRegex(ValueError, message):
                        audit.audit_input()
        with edited("UpperScale", "Full", lambda text: "theorem early : True := True.intro\n" + text):
            with self.assertRaisesRegex(ValueError, "Declaration before the namespace"):
                audit.audit_input()

    def test_private_declarations_are_not_roots(self):
        _, roots = audit.audit_input()
        with edited("UpperScale", "Full", lambda text: text.replace(
                "\nend ThresholdHC.UpperScale",
                "\nprivate theorem helper : True := True.intro\n\nend ThresholdHC.UpperScale")):
            _, changed = audit.audit_input()
        self.assertEqual(roots, changed)
        self.assertNotIn("ThresholdHC.UpperScale.helper", changed)

    def test_duplicate_declaration_rejected(self):
        with edited("UpperScale", "Full", lambda text: text.replace(
                "\nend ThresholdHC.UpperScale",
                "\ntheorem minimax_upper_12 : True := True.intro\n\nend ThresholdHC.UpperScale")):
            with self.assertRaisesRegex(ValueError, "Duplicate upper-scale declaration"):
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
