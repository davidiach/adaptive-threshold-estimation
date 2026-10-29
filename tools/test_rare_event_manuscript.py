"""Bind each rare-event genie bracket row to one verified certificate pair."""
import copy
import json
from pathlib import Path
import shutil
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest

import verify_rare_event_manuscript as tool

WITNESS_A = (0, 'upper_policy', 'perfect_labels_N1_B1000_upper.json')
WITNESS_B = (4, 'lower_certificate', '../certificates/three_scales_N8_B1000.json')


class BracketBindingTests(unittest.TestCase):
    def setUp(self):
        folder = TemporaryDirectory(prefix='rare-event-binding-')
        self.addCleanup(folder.cleanup)
        self.checks = Path(folder.name) / 'checks'
        shutil.copytree(tool.PACKAGE / 'v2/checks', self.checks)
        self.verifiers = tool.load_payload_verifiers(self.checks)
        self.laws = tool.bracket_case_laws(self.checks, self.verifiers[0].rational)
        self.table = tool.read_json(self.checks / 'optimized_genie/genie_bracket_results.json')

    def check(self, table):
        return tool.check_bracket_table(self.checks, table, self.laws, self.verifiers)

    def substituted(self, index, field, value):
        table = copy.deepcopy(self.table)
        table['results'][index][field] = value
        return table

    def test_verifiers_come_from_the_copy(self):
        for module in self.verifiers:
            self.assertTrue(Path(module.__file__).resolve().is_relative_to(self.checks.resolve()))
            self.assertNotIn(module.__name__, sys.modules)

    def test_every_stored_pair_binds(self):
        self.assertEqual(self.check(self.table), {'pairs': 9, 'cap_searches': 8})
        for row in self.table['results']:
            with self.subTest(case=row['case'], budget=row['budget'], cap=row['cap']):
                self.assertEqual(tool.bracket_pair_violations(
                    self.checks, row, self.laws, self.verifiers), [])

    def test_witness_a_upper_for_another_instance_rejected(self):
        with self.assertRaisesRegex(RuntimeError, r'row 0: identity: .* law, budget, cap'):
            self.check(self.substituted(*WITNESS_A))

    def test_witness_b_finite_cap_lower_rejected(self):
        with self.assertRaisesRegex(RuntimeError, r'row 4: scope: .*cap-N convex program'):
            self.check(self.substituted(*WITNESS_B))

    def test_witness_b_rejected_under_the_genuine_file_name(self):
        # Scope comes from verified content, not from the file's name or folder.
        shutil.copyfile(self.checks / 'certificates/three_scales_N8_B1000.json',
                        self.checks / 'optimized_genie/three_scales_N8_B1000_lower.json')
        with self.assertRaisesRegex(RuntimeError, r'row 4: scope: .*cap-N convex program'):
            self.check(self.table)

    def test_relabelled_finite_cap_lower_rejected(self):
        certificate = tool.read_json(self.checks / 'certificates/three_scales_N8_B1000.json')
        certificate['certificate_kind'] = tool.GENIE_LOWER_KIND
        (self.checks / 'optimized_genie/three_scales_N8_B1000_lower.json').write_text(
            json.dumps(certificate), encoding='utf-8')
        with self.assertRaisesRegex(RuntimeError, r'row 4: verification: .*genie boundary'):
            self.check(self.table)

    def test_scope_rechecked_without_trusting_the_label(self):
        # Even a lower verifier that trusted certificate_kind could not lend
        # a finite-cap certificate the uncapped scope.
        module = self.verifiers[0]

        def label_trusting_verify(certificate):
            result = module.verify({**certificate, 'certificate_kind': 'finite_cap'})
            return {**result, 'certificate_kind': tool.GENIE_LOWER_KIND,
                    'bound_scope': tool.GENIE_LOWER_SCOPE}

        trusting = SimpleNamespace(**{name: getattr(module, name) for name in (
            'rational', 'exact_latent_rewards', 'states_for', 'sqrt_lower_decimal')},
            verify=label_trusting_verify)
        with self.assertRaisesRegex(RuntimeError, r'row 4: scope: depth-cap potentials'):
            tool.check_bracket_table(self.checks, self.substituted(*WITNESS_B), self.laws,
                                     (trusting, self.verifiers[1]))

    def test_upper_for_another_cap_rejected(self):
        table = self.substituted(4, 'upper_policy', 'three_scales_N4_B1000_upper.json')
        with self.assertRaisesRegex(RuntimeError, r'(?m)row 4: identity: .* differ in cap$'):
            self.check(table)

    def test_undeclared_model_field_rejected(self):
        path = self.checks / 'optimized_genie/one_gap_N4_B100_upper.json'
        policy = tool.read_json(path)
        policy['observation_model'] = 'erasure'
        path.write_text(json.dumps(policy), encoding='utf-8')
        with self.assertRaisesRegex(RuntimeError, r"row 0: schema: upper .*observation_model"):
            self.check(self.table)

    def test_stale_decision_or_display_rejected(self):
        for index, field, value in ((3, 'exact_factor_two_stopping_test', True),
                                    (4, 'program_bracket_ratio', 1.5),
                                    (4, 'certified_rms_upper_decimal', '0.025532071713')):
            with self.subTest(field=field), self.assertRaisesRegex(
                    RuntimeError, rf'row {index}: stale: .*{field}'):
                self.check(self.substituted(index, field, value))

    def test_cap_search_must_stop_at_first_pass(self):
        table = copy.deepcopy(self.table)
        table['results'][3], table['results'][4] = table['results'][4], table['results'][3]
        with self.assertRaisesRegex(RuntimeError, 'Caps do not increase'):
            self.check(table)

    def test_registered_controls_include_both_witnesses_and_are_rejected(self):
        controls = {control[:3]: control[3] for control in tool.BRACKET_BINDING_CONTROLS}
        self.assertEqual(controls[WITNESS_A], 'identity')
        self.assertEqual(controls[WITNESS_B], 'scope')
        self.assertEqual(tool.reject_binding_controls(
            self.checks, self.table, self.laws, self.verifiers), len(controls))


if __name__ == '__main__':
    unittest.main()
