"""Fail-closed checks for the selection-component audit, without invoking Lean."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_selection_approximation as audit


class SelectionAuditTests(unittest.TestCase):
    def test_live_specification_and_dependency_coverage(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 3)
        self.assertEqual(len(audit.dependency_order(paths)), 6)
        self.assertTrue(set(audit.EXACT_TARGETS) <= roots)
        source = audit.audit_source(roots)
        self.assertEqual(source.count("#print axioms "), len(roots))
        self.assertIsNone(audit.FORBIDDEN.search(audit.strip_comments(source)))

    def test_changed_statement_or_inherited_definition_is_rejected(self):
        original = audit.sha
        for target in (audit.SOURCE / "Model.lean",
                       audit.LEAN / "ThresholdHC/EntropyTailQuantile/CostEntropy.lean",
                       audit.LEAN / "ThresholdHC/BandCostSelection/Dynamic.lean",
                       audit.LEAN / "lean-toolchain"):
            with self.subTest(target=target):
                with patch.object(audit, "sha", side_effect=lambda p: "0"*64 if p == target else original(p)):
                    with self.assertRaisesRegex(ValueError, "Locked specification"):
                        audit.validate_sources()

    def test_missing_module_or_target_is_rejected(self):
        with patch.object(audit, "MODULES", audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, "unregistered"):
                audit.validate_sources()
        with patch.object(audit, "EXACT_TARGETS", {audit.PREFIX + "missing": "False"}):
            with self.assertRaisesRegex(ValueError, "missing declaration"):
                audit.validate_sources()

    def test_proof_escapes_are_rejected(self):
        original = Path.read_text
        for escape in ("example : False := by sorry", "axiom escape : False",
                       "example : False := by admit", "#guard_msgs in\nexample : False := by sorry"):
            with self.subTest(escape=escape):
                def altered(path, *args, **kwargs):
                    text = original(path, *args, **kwargs)
                    return text + "\n" + escape if path == audit.SOURCE / "Entropy.lean" else text
                with patch.object(Path, "read_text", altered):
                    with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                        audit.validate_sources()

    def test_warnings_errors_and_failed_builds_are_rejected(self):
        for report, code in (("file: warning: unused variable", 0), ("error: bad proof", 0), ("", 1)):
            with self.subTest(report=report, code=code):
                with self.assertRaisesRegex(ValueError, "errors or warnings"):
                    audit.reject_diagnostics(report, code)

    def test_missing_duplicate_or_extra_axioms_are_rejected(self):
        name = audit.PREFIX + "entropy_perturbation"
        good = f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertIn(name, audit.validate_reports(good, 0, {name}))
        for report in ("", good + "\n" + good, good.replace("propext", "sorryAx")):
            with self.subTest(report=report):
                with self.assertRaises(ValueError):
                    audit.validate_reports(report, 0, {name})


if __name__ == "__main__":
    unittest.main()
