"""Check the new source boundary; shared axiom-report guards have their own tests."""
import unittest
from unittest.mock import patch

import verify_critical_upper_components as audit


class CriticalUpperAuditTests(unittest.TestCase):
    def test_registered_sources_and_all_component_targets(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 26)
        self.assertIn(audit.PREFIX+'screen_population_work_le', roots)
        self.assertIn(audit.PREFIX+'screen_population_second_moment_le', roots)
        for name in ('criticalUnbiased_population_integrable', 'criticalUnbiased_population_mean',
                     'criticalUnbiased_population_second_moment', 'criticalUnbiased_population_work'):
            self.assertIn(audit.PREFIX+name, roots)
        self.assertIn(audit.PREFIX+'FixedConsumes.path_eq', roots)
        self.assertTrue(set(audit.EXACT_TARGETS) <= roots)

    def test_full_targets_cannot_be_missing_or_weakened(self):
        for targets in ({}, {audit.PREFIX+'critical_upper_bound': 'True'},
                        {audit.PREFIX+'critical_upper_bound': audit.PREFIX+'CriticalUpperStatement'}):
            with self.subTest(targets=targets), patch.object(audit, 'EXACT_TARGETS', targets):
                with self.assertRaisesRegex(ValueError, 'full-theorem target'):
                    audit.validate_sources()

    def test_changed_frozen_target_rejected(self):
        with patch.object(audit, 'sha', return_value='0'*64):
            with self.assertRaisesRegex(ValueError, 'specification changed'):
                audit.validate_sources()

    def test_missing_module_rejected(self):
        with patch.object(audit, 'MODULES', audit.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, 'unregistered'):
                audit.validate_sources()

    def test_dependency_order_rejected(self):
        reordered = list(audit.MODULES)
        reordered[1], reordered[2] = reordered[2], reordered[1]
        with patch.object(audit, 'MODULES', tuple(reordered)):
            with self.assertRaisesRegex(ValueError, 'dependency order'):
                audit.validate_sources()


if __name__ == '__main__':
    unittest.main()
