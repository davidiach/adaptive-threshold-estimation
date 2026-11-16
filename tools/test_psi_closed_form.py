"""Reject changed statements, missing targets, hidden modules and unsound reports."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_psi_closed_form as audit
import verify_blind_upper_components as shared


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class PsiClosedFormAuditTests(unittest.TestCase):
    def test_every_declaration_is_a_root_and_every_target_is_restated(self):
        source, roots = audit.audit_input()
        for theorem, statement in audit.TARGETS.items():
            self.assertIn(audit.PREFIX + theorem, roots)
            self.assertIn(audit.PREFIX + statement, roots)
            self.assertIn(f"example : {statement} := {theorem}", source)
        for helper in ("inverseSquareCost", "selectionZero", "quantileZero",
                       "rareObjective_le_zero", "rarePsi_le_selectionZero", "sub_quantileCore",
                       "cutoff_lt_threshold", "kernel_pointwise", "root_sum_le",
                       "closed_form_real", "quantile_form_le"):
            self.assertIn(audit.PREFIX + helper, roots)
        self.assertEqual(source.count("#print axioms "), len(roots))
        # The inline statements carry the constant, every hypothesis and the
        # definitions of the entropy-free functionals literally.
        self.assertEqual(source.count("ENNReal.ofReal (Real.sqrt 2) * rarePsi"), 1)
        self.assertEqual(source.count("(hρ4 : ρ ≤ 1/4)"), 3)
        self.assertEqual(source.count("ENNReal.ofReal (((d : ℝ)⁻¹)^2)"), 9)
        exact = audit.EXACT
        for name in ("inverseSquareCost", "selectionZero", "quantileZero"):
            self.assertNotIn(name, exact)
        self.assertIn("quantileThreshold μ ρ ≤ 1 / Real.sqrt B", source)
        shared.validate_reports(report(roots), 0, roots)

    def test_changed_specification_rejected(self):
        real_sha = audit.sha
        changed = lambda p: "0" * 64 if p == audit.SOURCES / "Specification.lean" else real_sha(p)
        with patch.object(audit, "sha", side_effect=changed):
            with self.assertRaisesRegex(ValueError, "Changed Psi closed-form statement"):
                audit.audit_input()

    def test_hidden_or_missing_module_rejected(self):
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

    def test_missing_target_theorem_rejected(self):
        real_read = Path.read_text

        def renamed(path, *args, **kwargs):
            text = real_read(path, *args, **kwargs)
            if path == audit.SOURCES / "Full.lean":
                return text.replace("theorem psi_closed_form", "theorem unrelated")
            return text

        with patch.object(Path, "read_text", renamed):
            with self.assertRaisesRegex(ValueError, "Missing Psi closed-form target"):
                audit.audit_input()

    def test_proof_escape_rejected(self):
        real_read = Path.read_text

        def escaped(path, *args, **kwargs):
            text = real_read(path, *args, **kwargs)
            return text + "\ntheorem bad : False := sorry\n" if path == audit.SOURCES / "Full.lean" else text

        with patch.object(Path, "read_text", escaped):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.audit_input()

    def test_unsound_reports_rejected(self):
        _source, roots = audit.audit_input()
        one = sorted(roots)[0]
        cases = (
            (report(roots), 1, "exited unsuccessfully"),
            (report(roots - {one}), 0, "Missing or unexpected"),
            (report(roots, "propext, sorryAx"), 0, "Disallowed transitive axiom"),
            (report(roots) + "warning: declaration uses `sorry`\n", 0, "uses sorry"),
        )
        for output, code, message in cases:
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    shared.validate_reports(output, code, roots)


if __name__ == "__main__":
    unittest.main()
