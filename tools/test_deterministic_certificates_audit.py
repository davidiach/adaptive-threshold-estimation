"""Guard the exact statements, complete registry and source-identity boundary."""
from pathlib import Path
import unittest
from unittest.mock import patch

import verify_deterministic_certificates as audit
from verify_blind_upper_components import validate_reports


class DeterministicAuditTests(unittest.TestCase):
    def test_complete_scope(self):
        source, roots = audit.audit_input()
        self.assertEqual(source.count("example "), audit.EXACT_COUNT)
        self.assertEqual(source.count("#print axioms "), len(roots))
        for target in ("sqrtCheck_sound", "sqrtPrecisionCheck_sound", "logCheck_sound",
                       "check_sound", "accepted_sound", "entropyExpr_eval", "entropy_accepted_sound"):
            self.assertIn(audit.PREFIX+target, roots)
        for boundary in ("min 1 (Real.sqrt", "costEntropy", "accepted e claimed c = true"):
            self.assertIn(boundary, audit.EXACT)

    def test_changed_source_rejected(self):
        with patch.object(audit, "sha", return_value="0"*64):
            with self.assertRaisesRegex(ValueError, "Changed deterministic-checker"):
                audit.audit_input()

    def test_snapshot_covers_execution_sources(self):
        hashes = audit.input_hashes()
        for path in ("toolkit/threshold_toolkit/deterministic_certificates.py",
                     "toolkit/threshold_toolkit/rare_event_functional.py",
                     "toolkit/threshold_toolkit/__init__.py",
                     "tools/verify_deterministic_certificates.py",
                     "lean/ThresholdHC/DeterministicCertificates/SPECIFICATION.json"):
            self.assertIn(path, hashes)
        with patch.object(audit, "sha", return_value="0"*64):
            self.assertNotEqual(hashes, audit.input_hashes())

    def test_extra_module_rejected(self):
        original = Path.glob
        def extra(path, pattern):
            found = list(original(path, pattern))
            return found+[audit.SOURCES/"Hidden.lean"] if path == audit.SOURCES else found
        with patch.object(Path, "glob", extra):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()

    def test_registry_and_escapes(self):
        original = Path.read_text
        for suffix, message in [("\ntheorem bad : False := sorry\n", "Forbidden proof escape"),
                                ("\nprivate theorem hidden : True := True.intro\n", "registry cannot read")]:
            def altered(path, *args, **kwargs):
                text = original(path, *args, **kwargs)
                return text+suffix if path == audit.SOURCES/"Entropy.lean" else text
            with patch.object(Path, "read_text", altered):
                with self.assertRaisesRegex(ValueError, message):
                    audit.audit_input()

    def test_incomplete_or_unsound_reports(self):
        _, roots = audit.audit_input()
        report = "".join(f"'{r}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                         for r in sorted(roots))
        validate_reports(report, 0, roots)
        for text, code in [(report, 1), ("", 0), (report.replace("propext", "sorryAx"), 0),
                           (report+"warning: declaration uses `sorry`\n", 0)]:
            with self.assertRaises(ValueError):
                validate_reports(text, code, roots)


if __name__ == "__main__":
    unittest.main()
