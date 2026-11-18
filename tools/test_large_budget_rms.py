"""Regression checks for changed targets, omitted roots and proof escapes."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_large_budget_rms as audit
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


class LargeBudgetRMSAuditTests(unittest.TestCase):
    def test_targets_and_components_are_independently_restated(self):
        source, roots = audit.audit_input()
        for theorem, statement in audit.TARGETS.items():
            self.assertIn(audit.PREFIX + theorem, roots)
            self.assertIn(audit.PREFIX + statement, roots)
            self.assertIn(f"example : LargeBudgetRMS.{statement} := LargeBudgetRMS.{theorem}", source)
            self.assertRegex(audit.TARGETS_EXACT, rf":=\s*LargeBudgetRMS\.{theorem}\n")
        for name in audit.COMPONENTS:
            self.assertIn(audit.COMPONENT_PREFIX + name, roots)
            self.assertRegex(audit.COMPONENTS_EXACT, rf":=\s*@?{name}\n")
        self.assertEqual(len(audit.TARGETS), 4)
        self.assertEqual(len(audit.COMPONENTS), 20)
        self.assertEqual(source.count("\nexample"), audit.EXACT_COUNT + len(audit.TARGETS))
        self.assertEqual(source.count("#print axioms "), len(roots))
        for text in ("(175198/1000000 : ℝ)) ≤ minimaxRisk μ B ∧",
                     "(17807955/100000000 : ℝ)) ≤ selectedMinimaxRisk μ B",
                     "minimaxRisk (Measure.dirac (⟨1/5, by norm_num⟩ : Gap)) 25 ≤\n"
                     "    ENNReal.ofReal (186752/1000000 : ℝ)",
                     "≤ minimaxRisk μ B) → c ≤ 186752/1000000",
                     "≤ revealedMinimaxRisk μ B ∧"):
            self.assertIn(text, audit.TARGETS_EXACT)
        for text in ("HardBudget.PathwiseCap pilotEstimator 25",
                     "= 348763093753675683898541718818533/10^34"):
            self.assertIn(text, audit.COMPONENTS_EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_every_module_is_imported_and_replayed(self):
        source, _ = audit.audit_input()
        for name in audit.MODULES:
            self.assertIn(f"import {audit.PREFIX}{name}\n", source)
        self.assertEqual(audit.replay_modules(), [audit.PREFIX + name for name in audit.MODULES])
        self.assertEqual(len(audit.MODULES), 28)

    def test_research_namespaces_are_kept(self):
        _, roots = audit.audit_input()
        for family in ("LargeBudget", "MultiBias", "Pilot", "Revisit", "Revisit.IntPoly"):
            self.assertTrue(any(root.startswith(f"ThresholdHC.SharpRMS.{family}.") for root in roots))
        self.assertIn(audit.PREFIX + "fifthGap", roots)

    def test_changed_specification_rejected(self):
        with patch.object(audit, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed large-budget RMS statement"):
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
        for module, old in (("Full", "theorem bracket_upper"),
                            ("MultiBiasBounds", "theorem lower_25"),
                            ("PilotWitness", "theorem pilot_upper_25")):
            with self.subTest(old=old), edited(module, lambda text: text.replace(old, "theorem unrelated")):
                with self.assertRaisesRegex(ValueError, "Missing large-budget RMS target"):
                    audit.audit_input()

    def test_unrestated_component_rejected(self):
        with patch.object(audit, "COMPONENTS", audit.COMPONENTS + ("Pilot.pilot_table",)):
            with self.assertRaisesRegex(ValueError, "Missing large-budget RMS target"):
                audit.audit_input()
        with patch.object(audit, "COMPONENTS_EXACT",
                          audit.COMPONENTS_EXACT.replace("Pilot.pilot_cap\n", "Pilot.pilot_budget\n")):
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
            with self.subTest(addition=addition), edited("PilotCertificate", lambda text: text + addition):
                with self.assertRaisesRegex(ValueError, message):
                    audit.audit_input()
        with edited("Full", lambda text: "theorem early : True := True.intro\n" + text):
            with self.assertRaisesRegex(ValueError, "Declaration before the namespace"):
                audit.audit_input()

    def test_private_declarations_are_not_roots(self):
        _, roots = audit.audit_input()
        with edited("Full", lambda text: text.replace(
                "\nend ThresholdHC.LargeBudgetRMS",
                "\nprivate theorem helper : True := True.intro\n\nend ThresholdHC.LargeBudgetRMS")):
            _, changed = audit.audit_input()
        self.assertEqual(roots, changed)
        self.assertNotIn(audit.PREFIX + "helper", changed)

    def test_duplicate_declaration_rejected(self):
        with edited("Full", lambda text: text.replace(
                "\nend ThresholdHC.LargeBudgetRMS",
                "\ntheorem bracket_lower : True := True.intro\n\nend ThresholdHC.LargeBudgetRMS")):
            with self.assertRaisesRegex(ValueError, "Duplicate large-budget RMS declaration"):
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
