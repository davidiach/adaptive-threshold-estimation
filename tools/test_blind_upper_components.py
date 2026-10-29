"""Reject incomplete, misleading, or untrusted component audit evidence."""
import copy
import json
import unittest
from unittest.mock import patch

import verify_blind_upper_components as audit

from verify_blind_upper_components import REGISTRY, validate_reports, validate_sources


class BlindUpperAuditTests(unittest.TestCase):
    def setUp(self):
        self.registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
        self.roots = set(self.registry["roots"])
        self.lines = [f"'{r}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                      for r in sorted(self.roots)]

    def test_complete_standard_reports_and_registered_sources(self):
        self.assertEqual(set(validate_reports("\n".join(self.lines), 0, self.roots)), self.roots)
        self.assertEqual(validate_sources(self.registry)[1], self.roots)

    def test_changed_specification_dependency_rejected(self):
        original = audit.sha
        model = audit.LEAN / 'ThresholdHC/Tier6/AlgorithmModel.lean'
        with patch.object(audit, 'sha', side_effect=lambda p: '0'*64 if p == model else original(p)):
            with self.assertRaisesRegex(ValueError, 'dependency changed'):
                validate_sources(self.registry)

    def test_imports_cannot_silently_escape_the_dependency_lock(self):
        self.assertEqual(audit.imports('  import ThresholdHC.Tier6.AlgorithmModel\n'),
                         ['ThresholdHC.Tier6.AlgorithmModel'])
        for source in ('import Mathlib ThresholdHC.Tier6.AlgorithmModel\n',
                       'import\n ThresholdHC.Tier6.AlgorithmModel\n'):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, 'import syntax'):
                audit.imports(source)

    def test_failed_command_cannot_supply_success_evidence(self):
        with self.assertRaises(ValueError):
            validate_reports("\n".join(self.lines), 1, self.roots)

    def test_missing_duplicate_extra_roots_rejected(self):
        for lines in (self.lines[:-1], self.lines + self.lines[:1],
                      self.lines + ["'unexpected' does not depend on any axioms"]):
            with self.subTest(lines=lines), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0, self.roots)

    def test_sorry_warning_rejected(self):
        # Anonymous examples are not axiom-audited, so the warning is the evidence.
        for warning in ("Audit.lean:3:0: warning: declaration uses `sorry`",
                        "Audit.lean:3:0: warning: declaration uses 'sorry'"):
            output = "\n".join(self.lines + [warning])
            with self.subTest(warning=warning), self.assertRaisesRegex(ValueError, "sorry"):
                validate_reports(output, 0, self.roots)

    def test_primed_root_names_are_read(self):
        output = "'A.foo'' depends on axioms: [propext]\n'A.bar' does not depend on any axioms"
        self.assertEqual(validate_reports(output, 0, {"A.foo'", "A.bar"}),
                         {"A.foo'": ["propext"], "A.bar": []})

    def test_proof_escapes_missed_by_the_frozen_pattern_rejected(self):
        hidden = "set_option debug.skipKernelTC true\ntheorem hidden : False := by sorry\n"
        for source in ("example : Statement := by admit\n",
                       'def a : String := "/-"\n' + hidden + 'def b : String := "-/"\n',
                       'def a : String := "--" ; run_cmd pure ()\n',
                       'def \u00ab/-\u00bb : Nat := 0\n' + hidden + 'def \u00ab-/\u00bb : Nat := 0\n',
                       'def \u00ab--\u00bb : Nat := 0 ; run_cmd pure ()\n',
                       '#print "\'A.foo\' does not depend on any axioms"\n'):
            with self.subTest(source=source):
                self.assertIsNotNone(audit.FORBIDDEN.search(audit.strip_comments(source)))
        self.assertIsNone(audit.FORBIDDEN.search(audit.strip_comments(
            "/- \"quoted\" admit -/\ntheorem admits_x' : True := trivial -- \"note\"\n")))

    def test_sorry_warning_cannot_be_silenced(self):
        # The frozen pattern's \bsorry\b also matches the option name.
        for option in ("warn.sorry", "«warn.sorry»", "«warn».«sorry»"):
            source = f"set_option {option} false in\nexample : Statement := by stop rfl\n"
            with self.subTest(option=option):
                self.assertIsNotNone(audit.TIER6_FORBIDDEN.search(audit.strip_comments(source)))
                self.assertIsNotNone(audit.FORBIDDEN.search(audit.strip_comments(source)))

    def test_nonstandard_axioms_rejected(self):
        for axiom in ("sorryAx", "untrusted_assumption"):
            lines = self.lines.copy()
            lines[0] = lines[0].replace("[propext,", f"[{axiom}, propext,")
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0, self.roots)

    def test_unrelated_critical_upper_cannot_be_promoted(self):
        changed = copy.deepcopy(self.registry)
        changed['full_critical_upper_verified'] = True
        with self.assertRaises(ValueError):
            validate_sources(changed)

    def test_full_theorem_requires_unchanged_exact_target(self):
        for targets in ({}, {'ThresholdHC.BlindUpper.distribution_blind_upper': 'True'}):
            changed = copy.deepcopy(self.registry)
            changed['exact_targets'] = targets
            with self.subTest(targets=targets), self.assertRaises(ValueError):
                validate_sources(changed)

    def test_qualified_execution_declarations_cannot_be_omitted(self):
        changed = copy.deepcopy(self.registry)
        changed['roots'].remove('ThresholdHC.BlindUpper.BatchConsumes.path_eq')
        with self.assertRaises(ValueError):
            validate_sources(changed)

    def test_changed_specification_and_missing_registration_rejected(self):
        for change in ("specification_sha256", "roots", "modules"):
            altered = copy.deepcopy(self.registry)
            if change == "specification_sha256":
                altered[change] = "0" * 64
            else:
                altered[change] = altered[change][:-1]
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_sources(altered)


if __name__ == "__main__":
    unittest.main()
