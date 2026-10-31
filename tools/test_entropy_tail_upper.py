"""Fail-closed checks for the full entropy-tail upper audit boundary."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_entropy_tail_upper as audit


class UpperAuditTests(unittest.TestCase):
    def test_full_target_registry(self):
        paths, roots = audit.validate_sources()
        self.assertEqual({p.parent.name for p in paths}, set(audit.GROUPS))
        self.assertTrue(set(audit.TARGETS) <= roots)
        self.assertIn("ThresholdHC.EntropyTailExecution.poissonPlan_squaredRisk", roots)
        self.assertIn("ThresholdHC.EntropyTailExecution.finite_entropy_three_piece", roots)

    def test_missing_exact_target_fails_closed(self):
        with patch.object(audit, "TARGETS", {"ThresholdHC.EntropyTailExecution.missing": "False"}):
            with self.assertRaisesRegex(ValueError, "Missing exact target"):
                audit.validate_sources()

    def test_old_short_and_full_namespaces_are_rejected(self):
        original = Path.read_text
        target = audit.LEAN / "ThresholdHC/EntropyTailUpper/BankErrors.lean"
        for reference in ("EntropyTail.band", "ThresholdHC.EntropyTail.band"):
            with self.subTest(reference=reference):
                def altered(path, *args, **kwargs):
                    source = original(path, *args, **kwargs)
                    return source + "\n#check " + reference if path == target else source
                with patch.object(Path, "read_text", altered):
                    with self.assertRaisesRegex(ValueError, "Unported entropy-tail namespace"):
                        audit.validate_sources()

    def test_execution_proof_escape_fails_closed(self):
        original = Path.read_text
        target = audit.LEAN / "ThresholdHC/EntropyTailExecution/UpperTheorem.lean"
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
