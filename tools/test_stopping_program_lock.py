"""Fail-closed checks for the stopping-program specification lock."""
import json
import unittest
from unittest.mock import patch

import stopping_program_lock as lock
import verify_finite_risk_certificate
import verify_stopping_dual
import verify_stopping_program_upper

AUDITS = (verify_stopping_dual, verify_stopping_program_upper, verify_finite_risk_certificate)


class StoppingProgramLockTests(unittest.TestCase):
    def test_current_lock_is_valid(self):
        lock.validate_stopping_specification()

    def test_changed_specification_is_rejected(self):
        original = lock.sha
        with patch.object(lock, "sha", side_effect=lambda p: "0" * 64 if p == lock.SPECIFICATION else original(p)):
            with self.assertRaisesRegex(ValueError, "Frozen stopping-program specification"):
                lock.validate_stopping_specification()

    def test_changed_dependency_is_rejected(self):
        freeze = json.loads(lock.FREEZE.read_text(encoding="utf-8"))
        first = sorted(freeze["dependency_sha256"])[0]
        freeze["dependency_sha256"][first] = "0" * 64
        original = lock.json.loads
        with patch.object(lock.json, "loads", side_effect=lambda text: freeze if text == lock.FREEZE.read_text(encoding="utf-8") else original(text)):
            with self.assertRaisesRegex(ValueError, "dependency changed"):
                lock.validate_stopping_specification()

    def test_every_target_audit_checks_the_lock(self):
        for audit in AUDITS:
            with self.subTest(audit=audit.__name__):
                with patch.object(audit, "validate_stopping_specification",
                                  side_effect=ValueError("Frozen stopping-program specification changed")):
                    with self.assertRaisesRegex(ValueError, "Frozen stopping-program"):
                        audit.validate_sources()


if __name__ == "__main__":
    unittest.main()
