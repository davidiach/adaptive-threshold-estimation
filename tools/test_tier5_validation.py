"""Failure-path regression tests for the separate Tier 5 kernel guard."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
import verify_tier5 as guard


class Tier5ValidationTests(unittest.TestCase):
    def test_nested_comments_do_not_hide_code(self):
        source = "/- outer /- nested -/ outer -/\ntheorem x : True := by trivial\n"
        self.assertIn("theorem x", guard.strip_comments(source))
        with self.assertRaises(ValueError):
            guard.strip_comments("/- unclosed")

    def test_unexpected_axiom_and_sorry_both_fail(self):
        for axioms in (["sorryAx"], ["custom", "sorryAx"], ["custom"]):
            self.assertFalse(guard.valid_audit(0, {"x": axioms}, {"x"}, True))

    def test_failed_incomplete_or_changed_audit_fails(self):
        good = {"x": ["propext", "Classical.choice", "Quot.sound"]}
        self.assertTrue(guard.valid_audit(0, good, {"x"}, True))
        self.assertFalse(guard.valid_audit(1, good, {"x"}, True))
        self.assertFalse(guard.valid_audit(0, good, {"x", "y"}, True))
        self.assertFalse(guard.valid_audit(0, good, {"x"}, False))

    def test_duplicate_reports_fail(self):
        text = "'x' does not depend on any axioms\n"
        with self.assertRaises(ValueError):
            guard.parse_reports(text + text)

    def test_proof_escapes_and_namespace_are_rejected(self):
        with TemporaryDirectory() as folder:
            path = Path(folder) / "Proof.lean"
            for body in ("theorem x : True := by sorry", "run_cmd pure ()",
                         "axiom x : False", "unsafe def x := 0", '#eval IO.println "fake"'):
                path.write_text("namespace ThresholdHC.Tier5\n" + body)
                with self.assertRaises(ValueError):
                    guard.declarations(path)
            path.write_text("namespace Wrong\ntheorem x : True := by trivial")
            with self.assertRaises(ValueError):
                guard.declarations(path)

    def test_exact_declaration_names(self):
        with TemporaryDirectory() as folder:
            path = Path(folder) / "Proof.lean"
            path.write_text("namespace ThresholdHC.Tier5\nnoncomputable def Model : Prop := True\n"
                            "@[simp] theorem correct : Model := by trivial\nend ThresholdHC.Tier5\n")
            self.assertEqual(guard.declarations(path),
                             ["ThresholdHC.Tier5.Model", "ThresholdHC.Tier5.correct"])

    def test_lock_rejects_changes_and_missing_dependency(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            spec = root / "lean/ThresholdHC/Tier5/Specification.lean"
            spec.parent.mkdir(parents=True)
            spec.write_text("namespace ThresholdHC.Tier5\ndef Target : Prop := True\n")
            (root / "tools").mkdir()
            (root / guard.MANIFEST).write_text("{}")
            (root / "tools/verify_tier5.py").write_text("# guard")
            (root / "FROZEN.sha256").write_text("")
            (root / "TIER3_FROZEN.sha256").write_text("")
            (root / "TIER4_FROZEN.sha256").write_text("")
            paths = ["lean/ThresholdHC/Tier5/Specification.lean", guard.MANIFEST,
                     "tools/verify_tier5.py", "FROZEN.sha256", "TIER3_FROZEN.sha256", "TIER4_FROZEN.sha256"]
            def save_locks():
                (root / guard.LOCK).write_text("\n".join(guard.sha(root / p) + "  " + p for p in paths))
            manifest = {"specification_module": "ThresholdHC.Tier5.Specification"}
            save_locks()
            self.assertEqual(len(guard.check_locks(manifest, root)), 6)
            spec.write_text(spec.read_text() + "-- changed bytes\n")
            with self.assertRaises(ValueError):
                guard.check_locks(manifest, root)
            dependency = root / "lean/ThresholdHC/Tier5/Model.lean"
            dependency.write_text("def Other : Prop := True\n")
            spec.write_text("import ThresholdHC.Tier5.Model\n" + spec.read_text())
            save_locks()
            with self.assertRaises(ValueError):
                guard.check_locks(manifest, root)

    def test_lock_cannot_escape_repository(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / guard.LOCK).write_text("0" * 64 + "  ../outside.lean\n")
            with self.assertRaises(ValueError):
                guard.read_locks(root)


if __name__ == "__main__":
    unittest.main()
