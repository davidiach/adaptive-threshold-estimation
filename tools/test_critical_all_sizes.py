"""Failure-path checks for the all-size theorem's target and model locks."""
import unittest
from unittest.mock import patch

import verify_critical_all_sizes as audit
import verify_blind_upper_components as shared


class AllSizesAuditTests(unittest.TestCase):
    def test_registration(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 8)
        self.assertEqual(len(audit.EXACT_TARGETS), 4)
        self.assertTrue(set(audit.EXACT_TARGETS) <= roots)

    def test_weakened_or_missing_target(self):
        for targets in ({}, {audit.PREFIX+'finite_gap_sign_entropy_all': 'True'}):
            with self.subTest(targets=targets), patch.object(audit, 'EXACT_TARGETS', targets):
                with self.assertRaisesRegex(ValueError, 'exact target'):
                    audit.validate_sources()

    def test_changed_specification(self):
        real_sha = audit.sha
        def changed(path):
            return '0'*64 if path == audit.SOURCE/'Specification.lean' else real_sha(path)
        with patch.object(audit, 'sha', side_effect=changed):
            with self.assertRaisesRegex(ValueError, 'specification changed'):
                audit.validate_sources()

    def test_changed_imported_cost_or_population_model(self):
        real_sha = shared.sha
        for rel in ('lean/ThresholdHC/CriticalEntropy/SignTest.lean',
                    'lean/ThresholdHC/CriticalEntropy/GoodGapModel.lean'):
            def changed(path):
                return '0'*64 if path == audit.ROOT/rel else real_sha(path)
            with self.subTest(path=rel), patch.object(shared, 'sha', side_effect=changed):
                with self.assertRaisesRegex(ValueError, 'dependency changed'):
                    audit.validate_sources()

    def test_missing_module(self):
        with patch.object(audit, 'MODULES', audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, 'unregistered'):
                audit.validate_sources()

    def test_dependency_order(self):
        with patch.object(audit, 'MODULES', tuple(reversed(audit.MODULES))):
            with self.assertRaisesRegex(ValueError, 'dependency order'):
                audit.validate_sources()


if __name__ == '__main__':
    unittest.main()
