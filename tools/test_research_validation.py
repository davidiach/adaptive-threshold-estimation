"""Tampering must be rejected by the integrated research identity guard."""
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_research as verifier


class ResearchIdentityTests(unittest.TestCase):
    def test_source_tampering_and_missing_file_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / 'proof.tex'
            source.write_bytes(b'reviewed proof')
            expected = {'proof.tex': hashlib.sha256(source.read_bytes()).hexdigest()}
            with patch.object(verifier, 'ROOT', root):
                self.assertEqual(verifier.verify_mapping(root, expected), 1)
                source.write_bytes(b'different proof')
                with self.assertRaisesRegex(RuntimeError, 'Identity mismatch'):
                    verifier.verify_mapping(root, expected)
                source.unlink()
                with self.assertRaisesRegex(RuntimeError, 'Identity mismatch'):
                    verifier.verify_mapping(root, expected)

    def test_empty_and_escaping_locks_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with patch.object(verifier, 'ROOT', root):
                with self.assertRaisesRegex(RuntimeError, 'Empty identity lock'):
                    verifier.verify_mapping(root, {})
                with self.assertRaisesRegex(RuntimeError, 'escapes repository'):
                    verifier.verify_mapping(root, {'../outside.tex': '0' * 64})


if __name__ == '__main__':
    unittest.main()
