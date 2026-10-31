"""Fail-closed registration checks for the frozen-interface compatibility proof."""
from pathlib import Path
import unittest
from unittest.mock import patch
import verify_entropy_tail_bridge as audit


class BridgeAuditTests(unittest.TestCase):
    def test_both_interfaces_and_upper_target_are_checked(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 13)
        self.assertIn(audit.PREFIX + "canonical_selection_eq", roots)
        self.assertEqual(audit.TARGETS[audit.PREFIX + "canonical_entropy_tail_upper"],
                         "ThresholdHC.EntropyTail.EntropyTailUpperStatement")

    def test_missing_module_is_rejected(self):
        with patch.object(audit, "MODULES", ("Compatibility",)):
            with self.assertRaisesRegex(ValueError, "unregistered"):
                audit.validate_sources()

    def test_bridge_proof_escape_is_rejected(self):
        original = Path.read_text
        target = audit.LEAN / "ThresholdHC/EntropyTailBridge/Upper.lean"
        def altered(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            return text + "\nexample : False := by sorry" if path == target else text
        with patch.object(Path, "read_text", altered):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.validate_sources()

    def test_canonical_lock_is_still_enforced(self):
        with patch.object(audit.canonical, "sha", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Frozen entropy-tail"):
                audit.validate_sources()


if __name__ == "__main__":
    unittest.main()
