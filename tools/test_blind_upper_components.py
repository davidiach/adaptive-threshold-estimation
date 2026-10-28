"""Reject incomplete, misleading, or untrusted component audit evidence."""
import copy
import json
import unittest

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

    def test_failed_command_cannot_supply_success_evidence(self):
        with self.assertRaises(ValueError):
            validate_reports("\n".join(self.lines), 1, self.roots)

    def test_missing_duplicate_extra_roots_rejected(self):
        for lines in (self.lines[:-1], self.lines + self.lines[:1],
                      self.lines + ["'unexpected' does not depend on any axioms"]):
            with self.subTest(lines=lines), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0, self.roots)

    def test_nonstandard_axioms_rejected(self):
        for axiom in ("sorryAx", "untrusted_assumption"):
            lines = self.lines.copy()
            lines[0] = lines[0].replace("[propext,", f"[{axiom}, propext,")
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                validate_reports("\n".join(lines), 0, self.roots)

    def test_component_evidence_cannot_promote_full_theorem(self):
        for flag in ("full_distribution_blind_upper_verified", "full_critical_upper_verified"):
            changed = copy.deepcopy(self.registry)
            changed[flag] = True
            with self.subTest(flag=flag), self.assertRaises(ValueError):
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
