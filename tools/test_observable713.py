"""Reject weakened 713/iff targets and altered observable experiment definitions."""
import unittest
from unittest.mock import patch

import verify_observable713 as audit
import verify_blind_upper_components as shared


class Observable713AuditTests(unittest.TestCase):
    def test_complete_registration(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 8)
        self.assertEqual(len(audit.EXACT_TARGETS), 2)
        self.assertTrue(set(audit.EXACT_TARGETS) <= roots)
        self.assertIn(audit.PREFIX + 'observable_unbiased_iff', roots)

    def test_weakened_or_missing_target_rejected(self):
        for targets in ({}, {audit.PREFIX + 'observable_713': 'True'},
                        {audit.PREFIX + 'observable_713': audit.PREFIX + 'Observable713Statement'}):
            with self.subTest(targets=targets), patch.object(audit, 'EXACT_TARGETS', targets):
                with self.assertRaisesRegex(ValueError, 'exact full target'):
                    audit.validate_sources()

    def test_changed_model_or_specification_rejected(self):
        real_sha = audit.sha
        for rel in audit.FROZEN:
            def changed(path):
                return '0' * 64 if path == audit.ROOT / rel else real_sha(path)
            with self.subTest(path=rel), patch.object(audit, 'sha', side_effect=changed):
                with self.assertRaisesRegex(ValueError, 'Frozen observable'):
                    audit.validate_sources()

    def test_changed_imported_experiment_rejected(self):
        real_sha = shared.sha
        for rel in ('lean/ThresholdHC/Tier6/AlgorithmCore.lean',
                    'lean/ThresholdHC/Tier6/AlgorithmModel.lean'):
            def changed(path):
                return '0' * 64 if path == audit.ROOT / rel else real_sha(path)
            with self.subTest(path=rel), patch.object(shared, 'sha', side_effect=changed):
                with self.assertRaisesRegex(ValueError, 'dependency changed'):
                    audit.validate_sources()

    def test_missing_module_rejected(self):
        with patch.object(audit, 'MODULES', audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, 'unregistered'):
                audit.validate_sources()

    def test_dependency_order_rejected(self):
        with patch.object(audit, 'MODULES', tuple(reversed(audit.MODULES))):
            with self.assertRaisesRegex(ValueError, 'dependency order'):
                audit.validate_sources()


if __name__ == '__main__':
    unittest.main()
