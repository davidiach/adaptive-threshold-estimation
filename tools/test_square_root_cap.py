"""Regression checks for changed targets, omitted roots and proof escapes."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_square_root_cap as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class SquareRootCapAuditTests(unittest.TestCase):
    def test_targets_are_independently_restated(self):
        source, roots = audit.audit_input()
        for theorem, statement in audit.TARGETS.items():
            self.assertIn(audit.PREFIX + theorem, roots)
            self.assertIn(audit.PREFIX + statement, roots)
            self.assertIn(f"example : {statement} := {theorem}", source)
        for name in ("square_root_cap_factor", "four_ninths_cap"):
            self.assertIn(audit.PREFIX + name, roots)
            self.assertIn(f"@{name}\n", audit.EXACT)
        self.assertEqual(audit.EXACT.count("\nexample"), audit.EXACT_COUNT)
        self.assertEqual(source.count("#print axioms "), len(roots))
        for text in ("B ≤ N*(k-1/k)^2", "ENNReal.ofReal k * genieValue μ ρ B N", "4*B/9 ≤ N",
                     "programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B", "ρ ≤ 1/2"):
            self.assertIn(text, audit.EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_changed_specification_rejected(self):
        with patch.object(audit, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed square-root cap statement"):
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

    def test_missing_target_and_escapes_rejected(self):
        real_read = Path.read_text
        for change, message in (
            (lambda text: text.replace("theorem four_ninths_cap", "theorem unrelated"), "Missing square-root cap target"),
            (lambda text: text + "\ntheorem bad : False := sorry\n", "Forbidden proof escape"),
            (lambda text: text + "\ninstance : Inhabited Nat := ⟨0⟩\n", "Declaration the registry cannot read"),
        ):
            def changed(path, *args, **kwargs):
                text = real_read(path, *args, **kwargs)
                return change(text) if path == audit.SOURCES / "Full.lean" else text

            with self.subTest(message=message), patch.object(Path, "read_text", changed):
                with self.assertRaisesRegex(ValueError, message):
                    audit.audit_input()

    def test_private_lemma_is_not_a_root(self):
        _, roots = audit.audit_input()
        self.assertNotIn(audit.PREFIX + "mixing_weight", roots)
        self.assertEqual(len(roots), 6)

    def test_missing_and_unsound_reports_rejected(self):
        _, roots = audit.audit_input()
        for output, code, message in (
            (report(roots), 1, "exited unsuccessfully"),
            (report(roots - {min(roots)}), 0, "Missing or unexpected"),
            (report(roots, "propext, sorryAx"), 0, "Disallowed transitive axiom"),
        ):
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    shared.validate_reports(output, code, roots)


if __name__ == "__main__":
    unittest.main()
