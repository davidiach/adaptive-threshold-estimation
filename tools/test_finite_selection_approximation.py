"""Reject weakened, incomplete or unsound finite-selection audit evidence."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_finite_selection_approximation as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class FiniteSelectionAuditTests(unittest.TestCase):
    def test_independent_scope_and_complete_registry(self):
        source, roots = audit.audit_input()
        self.assertEqual(source.count("example "), audit.EXACT_COUNT)
        self.assertEqual(source.count("#print axioms "), len(roots))
        self.assertIn("example : FiniteLawApproximationStatement := finite_law_approximation", source)
        for boundary in ("some (-2,0)", "(l:ℝ)/(1+ε/4) ≤ K", "K := (selection μ ρ B).toReal",
                         "selectionObjective μ ρ B (μ.restrict (traceSet xs))",
                         "rest.IsSuffix ms", "ms ≤ Q*S", "0 < ε → ε ≤ 1",
                         "1+M^2*(1+⌊Real.logb 2 R⌋₊)*(1+⌊Real.logb 2 (L*R)⌋₊)"):
            self.assertIn(boundary, audit.EXACT)
        shared.validate_reports(report(roots), 0, roots)

    def test_changed_statement_or_dependency_rejected(self):
        with patch.object(audit, "sha", return_value="0"*64):
            with self.assertRaisesRegex(ValueError, "Changed finite-selection specification"):
                audit.audit_input()

    def test_unregistered_and_missing_modules_rejected(self):
        original = Path.glob
        def extra(path, pattern):
            found = list(original(path, pattern))
            return found+[audit.SOURCES/"Hidden.lean"] if path == audit.SOURCES else found
        with patch.object(Path, "glob", extra):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()
        with patch.object(audit, "MODULES", audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()

    def test_renamed_main_target_rejected(self):
        original = Path.read_text
        def renamed(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            return text.replace("theorem finite_law_approximation", "theorem unrelated") \
                if path == audit.SOURCES/"Full.lean" else text
        with patch.object(Path, "read_text", renamed):
            with self.assertRaisesRegex(ValueError, "Missing finite-selection audit target"):
                audit.audit_input()

    def test_escapes_and_unreadable_declarations_rejected(self):
        original = Path.read_text
        for addition, message in (
            ("\ntheorem bad : False := sorry\n", "Forbidden proof escape"),
            ("\nprivate theorem hidden : True := True.intro\n", "Declaration the registry cannot read"),
        ):
            def changed(path, *args, **kwargs):
                text = original(path, *args, **kwargs)
                return text+addition if path == audit.SOURCES/"Full.lean" else text
            with self.subTest(addition=addition), patch.object(Path, "read_text", changed):
                with self.assertRaisesRegex(ValueError, message):
                    audit.audit_input()

    def test_unsound_or_incomplete_reports_rejected(self):
        _, roots = audit.audit_input()
        for text, code, message in (
            (report(roots), 1, "exited unsuccessfully"),
            (report(roots-{min(roots)}), 0, "Missing or unexpected"),
            (report(roots, "propext, sorryAx"), 0, "Disallowed transitive axiom"),
            (report(roots)+"warning: declaration uses `sorry`\n", 0, "uses sorry"),
        ):
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    shared.validate_reports(text, code, roots)


if __name__ == "__main__":
    unittest.main()
