"""Regression checks for changed targets, omitted roots and proof escapes."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_psi_sharpness as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PsiSharpnessAuditTests(unittest.TestCase):
    def test_targets_are_independently_restated(self):
        source, roots = audit.audit_input()
        for theorem, statement in audit.TARGETS.items():
            self.assertIn(audit.PREFIX + theorem, roots)
            self.assertIn(audit.PREFIX + statement, roots)
            self.assertIn(f"example : {statement} := {theorem}", source)
        for name in ("occupiedBandCount", "twoAtomLaw", "twoAtom_probability",
                     "twoAtom_tail", "twoAtom_core", "finite_support_entropy", "sharp_example"):
            self.assertIn(audit.PREFIX + name, roots)
        self.assertEqual(source.count("#print axioms "), len(roots))
        for text in ("Real.sqrt ((1 - ρ) / ρ)", "(d₁ : ℝ) / 2",
                     "(Function.support (bandCost (quantileCore μ ρ))).Finite",
                     "Real.log (Real.logb 2 (1 / quantileThreshold μ ρ))"):
            self.assertIn(text, audit.EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_changed_specification_rejected(self):
        with patch.object(audit, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed Psi sharpness statement"):
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
        real_read = Path.read_text

        def renamed(path, *args, **kwargs):
            text = real_read(path, *args, **kwargs)
            if path == audit.SOURCES / "TwoAtom.lean":
                return text.replace("theorem two_atom_sharpness", "theorem unrelated")
            return text

        with patch.object(Path, "read_text", renamed):
            with self.assertRaisesRegex(ValueError, "Missing Psi sharpness target"):
                audit.audit_input()

    def test_escapes_and_unregistered_declaration_forms_rejected(self):
        real_read = Path.read_text
        for addition, message in (
            ("\ntheorem bad : False := sorry\n", "Forbidden proof escape"),
            ("\nprivate theorem omitted : True := True.intro\n", "Declaration the registry cannot read"),
        ):
            def changed(path, *args, **kwargs):
                text = real_read(path, *args, **kwargs)
                return text + addition if path == audit.SOURCES / "Full.lean" else text

            with self.subTest(addition=addition), patch.object(Path, "read_text", changed):
                with self.assertRaisesRegex(ValueError, message):
                    audit.audit_input()

    def test_missing_and_unsound_reports_rejected(self):
        _, roots = audit.audit_input()
        for output, code, message in (
            (report(roots), 1, "exited unsuccessfully"),
            (report(roots - {min(roots)}), 0, "Missing or unexpected"),
            (report(roots, "propext, sorryAx"), 0, "Disallowed transitive axiom"),
            (report(roots) + "warning: declaration uses `sorry`\n", 0, "uses sorry"),
        ):
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    shared.validate_reports(output, code, roots)


if __name__ == "__main__":
    unittest.main()
