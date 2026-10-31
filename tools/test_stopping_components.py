"""Fail-closed checks for the stopping-program exact-target audit."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_stopping_components as audit


class StoppingAuditTests(unittest.TestCase):
    def test_required_targets_and_dotted_declarations(self):
        paths, roots = audit.validate_sources()
        self.assertEqual({p.parent.name for p in paths}, audit.GROUPS)
        self.assertTrue(audit.REQUIRED <= roots)
        self.assertIn("ThresholdHC.StoppingProgram.FlowCone.withOutputs", roots)
        self.assertIn("ThresholdHC.StoppingProgram.finite_slater_multipliers", roots)
        self.assertEqual(audit.EXACT.count("example :"), 12)

    def test_missing_target_fails_closed(self):
        with patch.object(audit, "REQUIRED", {"ThresholdHC.StoppingProgram.absent"}):
            with self.assertRaisesRegex(ValueError, "Missing required target"):
                audit.validate_sources()

    def test_proof_escape_fails_closed(self):
        original = Path.read_text
        target = audit.LEAN / "ThresholdHC/StoppingProgram/StrongDuality.lean"
        for escape in ("example : False := by sorry", "axiom escape : False",
                       "example : False := by admit", "#guard_msgs in\nexample : False := by sorry"):
            with self.subTest(escape=escape):
                def altered(path, *args, **kwargs):
                    source = original(path, *args, **kwargs)
                    return source + "\n" + escape if path == target else source
                with patch.object(Path, "read_text", altered):
                    with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                        audit.validate_sources()


if __name__ == "__main__":
    unittest.main()
