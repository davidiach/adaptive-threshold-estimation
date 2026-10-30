"""Fail-closed checks for the fractional rarity-support audit."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_rarity_support as audit


class RaritySupportAuditTests(unittest.TestCase):
    def test_full_target_registry(self):
        ordered, paths, roots = audit.validate_sources()
        self.assertTrue(audit.REQUIRED <= roots)
        self.assertTrue(set(paths) <= set(ordered))
        self.assertEqual(audit.EXACT.count("example :"), 2)
        self.assertTrue(audit.NEW_MODULES <= {p.stem for p in paths})

    def test_missing_target_fails_closed(self):
        with patch.object(audit, "REQUIRED", {"ThresholdHC.StoppingProgram.absent"}):
            with self.assertRaisesRegex(ValueError, "Missing exact target"):
                audit.validate_sources()

    def test_cutoff_proof_escape_fails_closed(self):
        original = Path.read_text
        target = audit.LEAN / "ThresholdHC/StoppingProgram/FractionalCutoff.lean"
        for escape in ("example : False := by sorry", "axiom escape : False",
                       "example : False := by admit", "#guard_msgs in\nexample : False := by sorry"):
            with self.subTest(escape=escape):
                def altered(path, *args, **kwargs):
                    source = original(path, *args, **kwargs)
                    return source + "\n" + escape if path == target else source
                with patch.object(Path, "read_text", altered):
                    with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                        audit.validate_sources()

    def test_exact_source_escape_fails_closed(self):
        with patch.object(audit, "EXACT", audit.EXACT + "\naxiom escape : False"):
            with self.assertRaisesRegex(ValueError, "Forbidden exact audit source"):
                audit.validate_sources()


if __name__ == "__main__":
    unittest.main()
