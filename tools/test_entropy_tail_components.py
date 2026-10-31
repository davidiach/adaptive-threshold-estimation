"""Fail-closed regression checks for the additive quantile audit."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_entropy_tail_components as audit


class EntropyTailAuditTests(unittest.TestCase):
    def test_current_registry_and_dependency_order(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 20)
        self.assertTrue(set(audit.EXACT_TARGETS) <= roots)
        ordered = audit.dependency_order(paths)
        self.assertEqual(set(ordered), audit.project_dependencies(paths))
        positions = {p: i for i, p in enumerate(ordered)}
        for path in ordered:
            for name in audit.imports(audit.strip_comments(path.read_text(encoding="utf-8"))):
                if name.startswith("ThresholdHC."):
                    self.assertLess(positions[audit.module_path(name)], positions[path])

    def test_changed_frozen_model_is_rejected(self):
        original = audit.original_sha
        model = audit.SOURCE / "Model.lean"
        with patch.object(audit, "original_sha", side_effect=lambda p: "0" * 64 if p == model else original(p)):
            with self.assertRaisesRegex(ValueError, "Frozen entropy-tail"):
                audit.validate_sources()

    def test_missing_target_is_rejected(self):
        with patch.object(audit, "EXACT_TARGETS", {audit.PREFIX + "missing": audit.PREFIX + "QuantileComparisonStatement"}):
            with self.assertRaisesRegex(ValueError, "missing declaration"):
                audit.validate_sources()

    def test_unregistered_module_is_rejected(self):
        with patch.object(audit, "MODULES", audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, "unregistered"):
                audit.validate_sources()

    def test_proof_escapes_are_rejected(self):
        original = Path.read_text
        target = audit.SOURCE / "QuantileComparison.lean"
        for escape in ("example : False := by sorry", "axiom escape : False",
                       "example : False := by admit", "#guard_msgs in\nexample : False := by sorry"):
            with self.subTest(escape=escape):
                def altered(path, *args, **kwargs):
                    text = original(path, *args, **kwargs)
                    return text + "\n" + escape if path == target else text
                with patch.object(Path, "read_text", altered):
                    with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                        audit.validate_sources()


if __name__ == "__main__":
    unittest.main()
