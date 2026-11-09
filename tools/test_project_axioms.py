"""Reject incomplete, unsound or malformed whole-project axiom reports."""
from pathlib import Path
import tempfile
import unittest

import verify_project_axioms as audit


def report(modules=3, constants=10, theorems=7, declared="[]",
           used="[propext, Classical.choice, Quot.sound]", offenders="[]"):
    return (f"PROJECT_AXIOMS modules={modules}\n"
            f"PROJECT_AXIOMS constants={constants}\n"
            f"PROJECT_AXIOMS theorems={theorems}\n"
            f"PROJECT_AXIOMS declared={declared}\n"
            f"PROJECT_AXIOMS used={used}\n"
            f"PROJECT_AXIOMS offenders={offenders}\n")


class ProjectAxiomAuditTests(unittest.TestCase):
    def test_every_source_file_is_a_module(self):
        modules = audit.project_modules()
        sources = list((audit.LEAN / "ThresholdHC").rglob("*.lean"))
        self.assertEqual(len(modules), len(sources) + 1)
        self.assertIn("ThresholdHC", modules)
        self.assertIn("ThresholdHC.Tier6.Full", modules)
        # The one file that no result audit imports must still be built.
        self.assertIn("ThresholdHC.Proofs.Tier2.ClassifierWorkBridge", modules)
        source = audit.audit_source(modules)
        for module in modules:
            self.assertIn(f"import {module}\n", source)
        self.assertTrue(source.rstrip().endswith("#project_axioms"))

    def test_new_file_becomes_a_module_without_registration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "ThresholdHC" / "New").mkdir(parents=True)
            (root / "ThresholdHC.lean").write_text("", encoding="utf-8")
            (root / "ThresholdHC" / "New" / "Lemma.lean").write_text("", encoding="utf-8")
            self.assertEqual(audit.project_modules(root), ["ThresholdHC", "ThresholdHC.New.Lemma"])
            (root / "ThresholdHC.lean").unlink()
            with self.assertRaisesRegex(ValueError, "missing project module"):
                audit.project_modules(root)

    def test_clean_report_accepted(self):
        result = audit.validate_report(report(), 0, 3)
        self.assertEqual((result["modules"], result["constants"], result["theorems"]), (3, 10, 7))
        self.assertEqual(result["used"], list(audit.ALLOWED))
        # A project whose proofs use fewer axioms is still clean.
        audit.validate_report(report(used="[propext]"), 0, 3)

    def test_unsound_or_incomplete_reports_rejected(self):
        clean = report()
        cases = (
            (clean, 1, 3, "exited unsuccessfully"),
            (clean + "warning: declaration uses `sorry`\n", 0, 3, "uses sorry"),
            (clean, 0, 4, "expected 4"),
            (report(theorems=0), 0, 3, "no project theorems"),
            (report(constants=0, theorems=0), 0, 3, "no project theorems"),
            (report(declared="[ThresholdHC.bad]"), 0, 3, "declare axioms"),
            (report(offenders="[ThresholdHC.bad]"), 0, 3, "disallowed axioms"),
            (report(used="[propext, sorryAx]"), 0, 3, "Disallowed transitive axiom"),
            (report(used="[Lean.ofReduceBool, propext]"), 0, 3, "Disallowed transitive axiom"),
            (clean.replace("PROJECT_AXIOMS offenders=[]\n", ""), 0, 3, "Missing or unexpected"),
            (clean + "PROJECT_AXIOMS extra=[]\n", 0, 3, "Missing or unexpected"),
            (clean + "PROJECT_AXIOMS used=[]\n", 0, 3, "Duplicate"),
            (clean.replace("constants=10", "constants=many"), 0, 3, "Malformed count"),
            (clean.replace("offenders=[]", "offenders=none"), 0, 3, "Malformed name list"),
            ("", 0, 3, "Missing or unexpected"),
        )
        for output, code, modules, message in cases:
            with self.subTest(message=message, output=output[-40:]):
                with self.assertRaisesRegex(ValueError, message):
                    audit.validate_report(output, code, modules)

    def test_failed_or_sorry_build_rejected(self):
        audit.check_build("Build completed successfully.\n", 0)
        with self.assertRaisesRegex(ValueError, "failed"):
            audit.check_build("error: build failed\n", 1)
        with self.assertRaisesRegex(ValueError, "uses sorry"):
            audit.check_build("warning: X.lean:3:8: declaration uses `sorry`\n", 0)

    def test_main_theorem_closure(self):
        closure = audit.import_closure(audit.MAIN_THEOREM)
        for module in (*audit.MAIN_THEOREM, "ThresholdHC.Tier6.AlgorithmModel",
                       "ThresholdHC.BlindUpper.Specification", "ThresholdHC.Statements2"):
            self.assertIn(module, closure)
        self.assertEqual(len(closure), len(set(closure)))
        self.assertTrue(set(closure) <= set(audit.project_modules()))
        self.assertNotIn("ThresholdHC.EntropyTail.Law", closure)
        with self.assertRaisesRegex(ValueError, "Missing project module"):
            audit.import_closure(("ThresholdHC.DoesNotExist",))


if __name__ == "__main__":
    unittest.main()
