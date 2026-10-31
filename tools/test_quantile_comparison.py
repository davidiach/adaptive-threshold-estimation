"""Reject weakened quantile-comparison targets and altered specification sources."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_quantile_comparison as audit


class QuantileComparisonAuditTests(unittest.TestCase):
    def test_complete_registration(self):
        paths, roots = audit.validate_sources()
        self.assertEqual(len(paths), len(audit.MODULES))
        self.assertEqual(len(audit.TARGETS), 1)
        self.assertTrue(set(audit.PROVED) <= roots)
        self.assertIn(audit.PREFIX + 'ScalarComparisonStatement', roots)

    def test_weakened_or_missing_target_rejected(self):
        mutations = [{}]
        for name in audit.TARGETS:
            mutations.append({k: v for k, v in audit.TARGETS.items() if k != name})
            mutations.append({**audit.TARGETS, name: 'True'})
        for targets in mutations:
            with self.subTest(targets=targets), patch.object(audit, 'TARGETS', targets):
                with self.assertRaisesRegex(ValueError, 'exact full target'):
                    audit.validate_sources()

    def test_unknown_or_duplicate_proved_target_rejected(self):
        for proved in (audit.PROVED + (audit.PREFIX + 'invented',),
                       audit.PROVED + 2 * tuple(audit.TARGETS)[:1]):
            with self.subTest(proved=proved), patch.object(audit, 'PROVED', proved):
                with self.assertRaisesRegex(ValueError, 'proved target'):
                    audit.validate_sources()

    def test_unregistered_or_missing_proof_rejected(self):
        unproved = sorted(set(audit.TARGETS) - set(audit.PROVED))
        if audit.PROVED:
            with patch.object(audit, 'PROVED', audit.PROVED[1:]):
                with self.assertRaisesRegex(ValueError, 'Unregistered proof'):
                    audit.validate_sources()
        if unproved:
            with patch.object(audit, 'PROVED', audit.PROVED + (unproved[0],)):
                with self.assertRaisesRegex(ValueError, 'missing declaration root'):
                    audit.validate_sources()

    def test_hidden_unregistered_target_declaration_rejected(self):
        real_read = type(audit.SOURCE).read_text
        target = audit.SOURCE / (audit.MODULES[-1] + '.lean')
        for short in sorted(t.removeprefix(audit.PREFIX) for t in set(audit.TARGETS) - set(audit.PROVED)):
            for planted_line in (f'protected theorem {short} : True := trivial',
                                 f'theorem {audit.PREFIX}{short} : True := trivial',
                                 f'@[simp] private lemma {short} : True := trivial'):
                def planted(self, *args, **kwargs):
                    text = real_read(self, *args, **kwargs)
                    return text + '\n' + planted_line + '\n' if self == target else text
                with self.subTest(line=planted_line), \
                        patch.object(type(audit.SOURCE), 'read_text', planted):
                    with self.assertRaisesRegex(ValueError, 'Unregistered proof'):
                        audit.validate_sources()

    def test_changed_freeze_record_rejected(self):
        record = json.loads(audit.FREEZE.read_text(encoding='utf-8'))
        name = sorted(record['targets'])[0]
        mutations = [
            ('exact full target', {**record, 'targets': {}}),
            ('exact full target', {**record, 'targets': {**record['targets'], name: 'True'}}),
            ('Frozen quantile-comparison', {**record, 'source_sha256': {
                k: '0' * 64 for k in record['source_sha256']}}),
            ('Frozen quantile-comparison', {**record, 'source_sha256': {}}),
            ('dependency changed', {**record, 'dependency_sha256': {
                'lean/ThresholdHC/Statements.lean': '0' * 64}}),
        ]
        with tempfile.TemporaryDirectory() as directory:
            for message, changed in mutations:
                path = Path(directory) / 'freeze.json'
                path.write_text(json.dumps(changed), encoding='utf-8')
                with self.subTest(message=message), patch.object(audit, 'FREEZE', path):
                    with self.assertRaisesRegex(ValueError, message):
                        audit.validate_sources()

    def test_changed_specification_rejected(self):
        real_sha = audit.sha
        for rel in audit.FROZEN:
            def changed(path):
                return '0' * 64 if path == audit.ROOT / rel else real_sha(path)
            with self.subTest(path=rel), patch.object(audit, 'sha', side_effect=changed):
                with self.assertRaisesRegex(ValueError, 'Frozen quantile-comparison'):
                    audit.validate_sources()

    def test_new_project_import_in_specification_rejected(self):
        # The lock records no project dependencies; importing one changes the target's meaning.
        real_read = type(audit.SOURCE).read_text
        specification = audit.SOURCE / 'Specification.lean'

        def planted(self, *args, **kwargs):
            text = real_read(self, *args, **kwargs)
            return 'import ThresholdHC.Statements\n' + text if self == specification else text
        with patch.object(type(audit.SOURCE), 'read_text', planted):
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

    def test_proof_escape_in_registered_module_rejected(self):
        real_read = type(audit.SOURCE).read_text
        for module in audit.MODULES:
            target = audit.SOURCE / (module + '.lean')

            def planted(self, *args, **kwargs):
                text = real_read(self, *args, **kwargs)
                return text + '\nrun_cmd pure ()\n' if self == target else text
            with self.subTest(module=module), patch.object(type(audit.SOURCE), 'read_text', planted):
                with self.assertRaisesRegex(ValueError, 'Forbidden proof escape'):
                    audit.validate_sources()

    def test_dependency_order_rejected(self):
        if len(audit.MODULES) < 2:
            self.skipTest('a single registered module has no order to break')
        with patch.object(audit, 'MODULES', tuple(reversed(audit.MODULES))):
            with self.assertRaisesRegex(ValueError, 'dependency order'):
                audit.validate_sources()

    def test_incomplete_or_nonstandard_axiom_reports_rejected(self):
        roots = set(audit.TARGETS) | {audit.PREFIX + 'ScalarComparisonStatement'}
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
