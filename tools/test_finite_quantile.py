"""Reject a finite-quantile audit whose exact statements were dropped or changed."""
import hashlib
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_finite_quantile as audit


def with_audit_bytes(change):
    """Patch reads of the audit file only; every other file is read unchanged."""
    real_bytes, real_text = Path.read_bytes, Path.read_text

    def read_bytes(path):
        data = real_bytes(path)
        return change(data.decode("utf-8")).encode("utf-8") if path == audit.AUDIT else data

    def read_text(path, *args, **kwargs):
        text = real_text(path, *args, **kwargs)
        return change(text) if path == audit.AUDIT else text

    return patch.multiple(Path, read_bytes=read_bytes, read_text=read_text)


class FiniteQuantileAuditTests(unittest.TestCase):
    def test_current_sources_accepted(self):
        roots = audit.validate_sources()
        self.assertIn(audit.PREFIX + "direct_finite_law", roots)
        self.assertIn(audit.PREFIX + "DirectFiniteLawStatement", roots)

    def test_deleted_exact_statements_rejected(self):
        def without_examples(text):
            start = text.index("example ")
            return text[:start] + text[text.index("#print axioms"):]

        with with_audit_bytes(without_examples):
            with self.assertRaisesRegex(ValueError, "audit file changed"):
                audit.validate_sources()
        # Even with the recorded hash updated to match, the statements must be there.
        stripped = without_examples(audit.AUDIT.read_text(encoding="utf-8")).encode("utf-8")
        with with_audit_bytes(without_examples), \
                patch.object(audit, "AUDIT_SHA256", hashlib.sha256(stripped).hexdigest()):
            with self.assertRaisesRegex(ValueError, "lacks its exact statements"):
                audit.validate_sources()

    def test_weakened_exact_statement_rejected(self):
        weaken = lambda text: text.replace("example ", "example (_ : False) ", 1)
        with with_audit_bytes(weaken):
            with self.assertRaisesRegex(ValueError, "audit file changed"):
                audit.validate_sources()

    def test_changed_specification_rejected(self):
        with patch.object(audit, "SPEC_SHA256", "0" * 64):
            with self.assertRaisesRegex(ValueError, "differs from the statement"):
                audit.validate_sources()


if __name__ == "__main__":
    unittest.main()
