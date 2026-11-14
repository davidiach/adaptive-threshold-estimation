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
        self.assertTrue(source.rstrip().endswith("#project_axioms\n#project_definitions"))

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

    def test_import_closure_fails_closed_on_unreadable_imports(self):
        # An indented import or two modules on one line would otherwise be
        # skipped silently, and the replay would omit their modules.
        for line in ("  import ThresholdHC.B\n", "import ThresholdHC.B import ThresholdHC.C\n"):
            with self.subTest(line=line), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "ThresholdHC").mkdir()
                (root / "ThresholdHC" / "A.lean").write_text(line, encoding="utf-8")
                (root / "ThresholdHC" / "B.lean").write_text("", encoding="utf-8")
                (root / "ThresholdHC" / "C.lean").write_text("", encoding="utf-8")
                if line.startswith(" "):
                    self.assertEqual(audit.import_closure(("ThresholdHC.A",), root),
                                     ["ThresholdHC.A", "ThresholdHC.B"])
                else:
                    with self.assertRaisesRegex(ValueError, "Unsupported import syntax"):
                        audit.import_closure(("ThresholdHC.A",), root)

    def test_instances_are_named_global_default_and_not_new_orphans(self):
        orphans = "".join(f"PROJECT_INSTANCE {name} global 1000 orphan\n"
                          for name in sorted(audit.ORPHAN_INSTANCES))
        clean = ("PROJECT_INSTANCE ThresholdHC.A.law_probability global 1000 prop\n"
                 "PROJECT_INSTANCE ThresholdHC.A.controlSpace global 1000 data\n" + orphans)
        self.assertEqual(len(audit.validate_instances(clean)), 2 + len(audit.ORPHAN_INSTANCES))
        cases = (
            ("", "report is missing"),
            (clean + "PROJECT_INSTANCE Mathlib.foo global 1000 data\n", "outside the project"),
            (clean + "PROJECT_INSTANCE [anonymous] global 1000 data\n", "outside the project"),
            (clean + "PROJECT_INSTANCE ThresholdHC.A.hijack scoped:ThresholdHC.A 1000 data\n",
             "Scoped project instance"),
            (clean + "PROJECT_INSTANCE ThresholdHC.A.hijack global 10000 data\n", "priority"),
            (clean + "PROJECT_INSTANCE ThresholdHC.A.hijack global 1000 orphan\n",
             "New data-carrying instance"),
            (clean.replace(orphans.splitlines(True)[0], ""), "orphan instance missing"),
        )
        for output, message in cases:
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    audit.validate_instances(output)

    def test_definition_fingerprints_are_read_completely(self):
        output = ("PROJECT_DEFINITIONS count=2\n"
                  "PROJECT_DEFINITION ThresholdHC.A.f 12:34\nPROJECT_DEFINITION ThresholdHC.A.g 5\n")
        self.assertEqual(audit.definition_fingerprints(output),
                         {"ThresholdHC.A.f": "12:34", "ThresholdHC.A.g": "5"})
        for bad, message in (
            (output.replace("count=2", "count=3"), "incomplete"),
            (output.replace("PROJECT_DEFINITIONS count=2\n", ""), "incomplete"),
            ("PROJECT_DEFINITIONS count=0\n", "incomplete"),
            (output.replace("count=2", "count=3") + "PROJECT_DEFINITION ThresholdHC.A.f 1\n",
             "Duplicate"),
        ):
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    audit.definition_fingerprints(bad)

    def test_locked_definitions_cannot_change_or_disappear(self):
        locked = {"ThresholdHC.A.f": "1:2", "ThresholdHC.A.g": "3:4"}
        self.assertEqual(audit.compare_definitions(locked, dict(locked)), [])
        self.assertEqual(audit.compare_definitions(locked, {**locked, "ThresholdHC.A.h": "5"}),
                         ["ThresholdHC.A.h"])
        with self.assertRaisesRegex(ValueError, "changed: ThresholdHC.A.f"):
            audit.compare_definitions(locked, {**locked, "ThresholdHC.A.f": "1:9"})
        with self.assertRaisesRegex(ValueError, "removed: ThresholdHC.A.g"):
            audit.compare_definitions(locked, {"ThresholdHC.A.f": "1:2"})

    def test_adding_definitions_keeps_existing_entries(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lock.json"
            lock = {"description": "test", "definitions": {"ThresholdHC.A.f": "1:2"}}
            actual = {"ThresholdHC.A.f": "1:2", "ThresholdHC.A.g": "3:4"}
            audit.add_definitions(path, lock, actual, ["ThresholdHC.A.g"])
            written = audit.read_lock(path)
            self.assertEqual(written["definitions"], actual)
            self.assertEqual(written["description"], "test")
            self.assertEqual(written["added"][-1]["count"], 1)

    def test_committed_lock_is_well_formed(self):
        lock = audit.read_lock(audit.DEFINITION_LOCK)
        self.assertGreater(len(lock["definitions"]), 2000)
        self.assertIn("ThresholdHC.KnownLawPlanner.quantilePlanEstimator", lock["definitions"])
        self.assertTrue(all(name.startswith("ThresholdHC.") or name.startswith("_private.ThresholdHC.")
                            for name in lock["definitions"]))


if __name__ == "__main__":
    unittest.main()
