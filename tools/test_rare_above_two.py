"""Reject weakened rare-event targets and altered observable experiment definitions."""
import unittest
from unittest.mock import patch

import verify_rare_above_two as audit
import verify_blind_upper_components as shared


class RareAboveTwoAuditTests(unittest.TestCase):
    def test_complete_registration(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), 54)
        self.assertEqual(len(audit.EXACT_TARGETS), 7)
        self.assertTrue(set(audit.EXACT_TARGETS) <= roots)
        self.assertIn(audit.PREFIX + 'above_two_minimax', roots)

    def test_weakened_or_missing_target_rejected(self):
        mutations = [{}]
        for name in audit.EXACT_TARGETS:
            mutations.append({k: v for k, v in audit.EXACT_TARGETS.items() if k != name})
            mutations.append({**audit.EXACT_TARGETS, name: 'True'})
        for targets in mutations:
            with self.subTest(targets=targets), patch.object(audit, 'EXACT_TARGETS', targets):
                with self.assertRaisesRegex(ValueError, 'exact full target'):
                    audit.validate_sources()

    def test_changed_model_or_specification_rejected(self):
        real_sha = audit.sha
        for rel in audit.FROZEN:
            def changed(path):
                return '0' * 64 if path == audit.ROOT / rel else real_sha(path)
            with self.subTest(path=rel), patch.object(audit, 'sha', side_effect=changed):
                with self.assertRaisesRegex(ValueError, 'Frozen rare-event'):
                    audit.validate_sources()

    def test_changed_imported_experiment_rejected(self):
        real_sha = shared.sha
        for rel in ('lean/ThresholdHC/RareAboveTwo/Model.lean',
                    'lean/ThresholdHC/Tier6/AlgorithmCore.lean',
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

    def test_unregistered_nested_module_rejected(self):
        real_rglob = type(audit.SOURCE).rglob

        def rglob(self, pattern):
            found = list(real_rglob(self, pattern))
            return found + [audit.SOURCE / 'Extra' / 'Hidden.lean'] if self == audit.SOURCE else found
        with patch.object(type(audit.SOURCE), 'rglob', rglob):
            with self.assertRaisesRegex(ValueError, 'unregistered'):
                audit.validate_sources()

    def test_proof_escape_in_registered_or_imported_module_rejected(self):
        real_read = type(audit.SOURCE).read_text
        for target in (audit.SOURCE / 'Full.lean', audit.ROOT / 'lean/ThresholdHC/Tier6/AlgorithmCore.lean'):
            def planted(self, *args, **kwargs):
                text = real_read(self, *args, **kwargs)
                return text + '\nrun_cmd pure ()\n' if self == target else text
            with self.subTest(path=target.name), patch.object(type(audit.SOURCE), 'read_text', planted):
                with self.assertRaisesRegex(ValueError, 'Forbidden proof escape'):
                    audit.validate_sources()

    def test_dependency_order_rejected(self):
        with patch.object(audit, 'MODULES', tuple(reversed(audit.MODULES))):
            with self.assertRaisesRegex(ValueError, 'dependency order'):
                audit.validate_sources()

    def test_incomplete_or_nonstandard_axiom_reports_rejected(self):
        roots = set(audit.EXACT_TARGETS)
        reports = [f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                   for name in sorted(roots)]
        text = "\n".join(reports)
        self.assertEqual(set(audit.validate_reports(text, 0, roots)), roots)
        mutations = ["\n".join(reports[:-1]), text + "\n" + reports[0],
                     text.replace('Quot.sound', 'sorryAx'),
                     text.replace('Quot.sound', 'inventedTheorem')]
        for output in mutations:
            with self.subTest(output=output), self.assertRaises(ValueError):
                audit.validate_reports(output, 0, roots)
        with self.assertRaises(ValueError):
            audit.validate_reports(text, 1, roots)


if __name__ == '__main__':
    unittest.main()
