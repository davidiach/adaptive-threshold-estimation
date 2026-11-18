"""Regression checks for changed targets, omitted roots and proof escapes."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_upper_mixture as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


def edited(module, change):
    """Patch for Path.read_text that edits one registered module."""
    real_read = Path.read_text

    def read(path, *args, **kwargs):
        text = real_read(path, *args, **kwargs)
        return change(text) if path == audit.SOURCES / f"{module}.lean" else text

    return patch.object(Path, "read_text", read)


class UpperMixtureAuditTests(unittest.TestCase):
    def test_targets_and_components_are_independently_restated(self):
        source, roots = audit.audit_input()
        for theorem, statement in audit.TARGETS.items():
            self.assertIn(audit.PREFIX + theorem, roots)
            self.assertIn(audit.PREFIX + statement, roots)
            self.assertIn(f"example : UpperMixture.{statement} := UpperMixture.{theorem}", source)
            self.assertRegex(audit.EXACT, rf":=\s*UpperMixture\.{theorem}\n")
        for name in audit.COMPONENTS:
            self.assertIn(audit.PREFIX + name, roots)
            self.assertRegex(audit.EXACT, rf":=\s*@?UpperMixture\.{name}\n")
        self.assertEqual(len(audit.TARGETS), 2)
        self.assertEqual(len(audit.COMPONENTS), 6)
        self.assertEqual(source.count("\nexample"), audit.EXACT_COUNT + len(audit.TARGETS))
        self.assertEqual(source.count("#print axioms "), len(roots))
        for text in ("minimaxRisk μ B ≤ ENNReal.ofReal (27*modulus μ (1/Real.sqrt B))",
                     "UniformBudget μ (rule B) B ∧",
                     "ENNReal.ofReal (UpperMixture.clip p) * expectedWork μ A₁ q +",
                     "squaredRisk (experimentLaw μ A₁ q) (populationOutput A₁) a +",
                     "N * (modulus μ (1 / Real.sqrt N)) ^ 2 ≤ B * (modulus μ (1 / Real.sqrt B)) ^ 2",
                     "ENNReal.ofReal ((19781/125) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2)",
                     "UniformBudget μ (UpperMixture.budgetMixture B) B",
                     "ENNReal.ofReal (27 * modulus μ (1 / Real.sqrt B))"):
            self.assertIn(text, audit.EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_every_module_is_imported_and_replayed(self):
        source, _ = audit.audit_input()
        for name in audit.MODULES:
            self.assertIn(f"import {audit.PREFIX}{name}\n", source)
        self.assertEqual(audit.replay_modules(), [audit.PREFIX + name for name in audit.MODULES])
        self.assertEqual(len(audit.MODULES), 3)

    def test_changed_specification_rejected(self):
        with patch.object(audit, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed upper-mixture statement"):
                audit.audit_input()

    def test_hidden_and_missing_modules_rejected(self):
        real_glob = Path.glob

        def extra(path, pattern):
            found = list(real_glob(path, pattern))
            return found + [audit.SOURCES / "Hidden.lean"] if path == audit.SOURCES else found

        with patch.object(Path, "glob", extra):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()
        with patch.object(audit, "MODULES", audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()

    def test_missing_target_rejected(self):
        for module, old in (("Full", "theorem minimax_upper_27"),
                            ("Mixture", "theorem mix_squaredRisk"),
                            ("Full", "theorem budgetMixture_uniformBudget")):
            with self.subTest(old=old), edited(module, lambda text: text.replace(old, "theorem unrelated")):
                with self.assertRaisesRegex(ValueError, "Missing upper-mixture target"):
                    audit.audit_input()

    def test_unrestated_component_rejected(self):
        with patch.object(audit, "COMPONENTS", audit.COMPONENTS + ("budget_scale",)):
            with self.assertRaisesRegex(ValueError, "Missing upper-mixture target"):
                audit.audit_input()
        with patch.object(audit, "EXACT",
                          audit.EXACT.replace("@UpperMixture.mix_squaredRisk\n", "@UpperMixture.mix_expectedWork\n")):
            with self.assertRaisesRegex(ValueError, "exactly one restated statement"):
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
            with self.subTest(addition=addition), edited("Mixture", lambda text: text + addition):
                with self.assertRaisesRegex(ValueError, message):
                    audit.audit_input()
        with edited("Full", lambda text: "theorem early : True := True.intro\n" + text):
            with self.assertRaisesRegex(ValueError, "Declaration before the namespace"):
                audit.audit_input()

    def test_private_declarations_are_not_roots(self):
        _, roots = audit.audit_input()
        with edited("Full", lambda text: text.replace(
                "\nend ThresholdHC.UpperMixture",
                "\nprivate theorem helper : True := True.intro\n\nend ThresholdHC.UpperMixture")):
            _, changed = audit.audit_input()
        self.assertEqual(roots, changed)
        self.assertNotIn(audit.PREFIX + "helper", changed)

    def test_duplicate_declaration_rejected(self):
        with edited("Full", lambda text: text.replace(
                "\nend ThresholdHC.UpperMixture",
                "\ntheorem minimax_upper_27 : True := True.intro\n\nend ThresholdHC.UpperMixture")):
            with self.assertRaisesRegex(ValueError, "Duplicate upper-mixture declaration"):
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
