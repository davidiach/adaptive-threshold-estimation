"""Regression checks for changed targets, omitted roots and proof escapes."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_confidence_transfer_steps as audit
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


class ConfidenceTransferStepsAuditTests(unittest.TestCase):
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
        for text in ("ENNReal.ofReal (1/8192) * rarePsi μ ρ (ThresholdHC.Confidence.confidenceScale B δ) ≤",
                     "ThresholdHC.HardBudget.PathwiseCap A ⌊B⌋₊ ∧",
                     "ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (C*z)",):
            self.assertIn(text, audit.EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_every_module_is_imported_and_replayed(self):
        source, _ = audit.audit_input()
        for module in audit.modules():
            self.assertIn(f"import ThresholdHC.{module}\n", source)
        self.assertEqual(audit.replay_modules(), ["ThresholdHC." + m for m in audit.modules()])
        self.assertEqual(len(audit.modules()), 4)

    def test_changed_specification_rejected(self):
        with patch.object(audit, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed confidence-transfer-steps specification"):
                audit.audit_input()

    def test_hidden_and_missing_modules_rejected(self):
        real_glob = Path.glob

        def extra(path, pattern):
            found = list(real_glob(path, pattern))
            return found + [audit.SOURCE / "Hidden.lean"] if path == audit.SOURCE else found

        with patch.object(Path, "glob", extra):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing ConfidenceTransferSteps"):
                audit.audit_input()
        with patch.object(audit, "NAMES", audit.NAMES[:-1]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing ConfidenceTransferSteps"):
                audit.audit_input()

    def test_missing_target_rejected(self):
        for module, old in (("Full", "theorem psi_confidence_null"),
                            ("Full", "theorem above_two_confidence"),
                            ("Lower", "theorem exact_power_confidence_lower"),
                            ("Upper", "theorem aboveTwoRate_confidence")):
            with self.subTest(old=old), edited(module, lambda text: text.replace(old, "theorem unrelated")):
                with self.assertRaisesRegex(ValueError, "Missing confidence-transfer-steps target"):
                    audit.audit_input()

    def test_unrestated_component_rejected(self):
        with patch.object(audit, "COMPONENTS", audit.COMPONENTS + ("ConfidenceTransferSteps.aboveTwoRate_scale",)):
            with self.assertRaisesRegex(ValueError, "exactly one restated statement"):
                audit.audit_input()
        with patch.object(audit, "EXACT", audit.EXACT.replace(
                "ConfidenceTransferSteps.confidence_resolution_rate\n", "ConfidenceTransferSteps.aboveTwoRate_scale\n")):
            with self.assertRaisesRegex(ValueError, "exactly one restated statement"):
                audit.audit_input()

    def test_declaration_outside_its_directory_namespace_rejected(self):
        with edited("Full", lambda text: text.replace(
                "namespace ThresholdHC.ConfidenceTransferSteps", "namespace ThresholdHC.PowerWindow").replace(
                "end ThresholdHC.ConfidenceTransferSteps", "end ThresholdHC.PowerWindow")):
            with self.assertRaisesRegex(ValueError, "must declare in ThresholdHC.ConfidenceTransferSteps"):
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
            for module in ("Lower", "Full"):
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
                "\nend ThresholdHC.ConfidenceTransferSteps",
                "\nprivate theorem helper : True := True.intro\n\nend ThresholdHC.ConfidenceTransferSteps")):
            _, changed = audit.audit_input()
        self.assertEqual(roots, changed)
        self.assertNotIn("ThresholdHC.ConfidenceTransferSteps.helper", changed)

    def test_duplicate_declaration_rejected(self):
        with edited("Full", lambda text: text.replace(
                "\nend ThresholdHC.ConfidenceTransferSteps",
                "\ntheorem above_two_confidence_family : True := True.intro\n\nend ThresholdHC.ConfidenceTransferSteps")):
            with self.assertRaisesRegex(ValueError, "Duplicate confidence-transfer-steps declaration"):
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
