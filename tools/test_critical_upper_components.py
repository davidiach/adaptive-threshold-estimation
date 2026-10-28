"""Check the new source boundary; shared axiom-report guards have their own tests."""
import unittest
from unittest.mock import patch

import verify_critical_upper_components as audit


class CriticalUpperAuditTests(unittest.TestCase):
    def test_registered_sources_and_all_component_targets(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 10)
        self.assertIn(audit.PREFIX+'screen_population_work_le', roots)
        self.assertIn(audit.PREFIX+'screen_population_second_moment_le', roots)

    def test_changed_frozen_target_rejected(self):
        with patch.object(audit, 'sha', return_value='0'*64):
            with self.assertRaisesRegex(ValueError, 'specification changed'):
                audit.validate_sources()

    def test_changed_specification_dependency_rejected(self):
        real = audit.sha
        rare = audit.LEAN / 'ThresholdHC/CriticalEntropy/CriticalRareModel.lean'
        with patch.object(audit, 'sha', side_effect=lambda p: '0'*64 if p == rare else real(p)):
            with self.assertRaisesRegex(ValueError, 'dependency changed'):
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
