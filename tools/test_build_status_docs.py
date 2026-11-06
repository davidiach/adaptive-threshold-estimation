"""Regression tests for the status summaries generated from status.json."""
import copy
import re
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_status_docs as docs  # noqa: E402
from build_v6 import load_status  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


class ConversionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.sources = Path(self.tmp.name) / "v6"
        self.sources.mkdir()
        (self.sources / "appendix-cap.tex").write_text(
            "\\section{Caps for $\\Psi$--rates}\n\\label{app:cap}\nText.\n", encoding="utf-8")
        self.document = Path(self.tmp.name) / "README.md"

    def tearDown(self):
        self.tmp.cleanup()

    def convert(self, phrase):
        return docs.latex_to_markdown(phrase, self.document, self.sources)

    def test_math_dashes_and_spaces(self):
        self.assertEqual(self.convert("the entropy--tail law with $10^{-17}$ and~$28000$"),
                         "the entropy–tail law with $10^{-17}$ and $28000$")

    def test_references_link_to_the_defining_section(self):
        self.assertEqual(self.convert("the results of \\cref{app:cap}"),
                         "the results of [Caps for $\\Psi$–rates](v6/appendix-cap.tex)")

    def test_unsupported_latex_fails_closed(self):
        for phrase in ("\\emph{x}", "a {group}", "math $|x|$", "a | b", "\\cref{app:none}"):
            with self.subTest(phrase):
                with self.assertRaises(ValueError):
                    self.convert(phrase)

    def test_duplicate_labels_fail(self):
        (self.sources / "other.tex").write_text("\\section{B}\\label{app:cap}\n", encoding="utf-8")
        with self.assertRaises(ValueError):
            docs.section_for("app:cap", self.sources)


class BlockTests(unittest.TestCase):
    def test_only_the_marked_block_changes(self):
        text = f"before\n{docs.BEGIN}\nold\n{docs.END}\nafter\n"
        self.assertEqual(docs.replace_block(text, "new\n", "doc"), "before\nnew\nafter\n")

    def test_missing_repeated_or_reversed_markers_fail(self):
        for text in ("no markers", f"{docs.BEGIN}\n{docs.BEGIN}\n{docs.END}\n",
                     f"{docs.END}\n{docs.BEGIN}\n"):
            with self.subTest(text[:12]):
                with self.assertRaises(ValueError):
                    docs.replace_block(text, "x\n", "doc")

    def test_check_detects_and_write_repairs_a_stale_summary(self):
        status = load_status()
        with tempfile.TemporaryDirectory() as tmp:
            document = Path(tmp) / "doc.md"
            document.write_text(f"intro\n{docs.BEGIN}\nstale\n{docs.END}\nend\n", encoding="utf-8")
            self.assertEqual(docs.update(status, (document,), write=False), [document])
            self.assertIn("stale", document.read_text(encoding="utf-8"))
            docs.update(status, (document,), write=True)
            self.assertEqual(docs.update(status, (document,), write=False), [])
            text = document.read_text(encoding="utf-8")
            self.assertTrue(text.startswith("intro\n") and text.endswith("end\n"))


class RepositoryTests(unittest.TestCase):
    def test_every_result_has_one_row_with_its_status(self):
        status = load_status()
        block = docs.render(status, ROOT / "README.md")
        rows = [line for line in block.splitlines() if line.startswith("| ") and "---" not in line][1:]
        self.assertEqual(len(rows), len(status["results"]))
        for key, line in zip(docs.ordered_keys(status), rows):
            self.assertIn(docs.STATUS_LABELS[status["results"][key]["status"]], line)

    def test_a_status_change_changes_the_summary(self):
        status = load_status()
        changed = copy.deepcopy(status)
        changed["results"]["psi-lower-bound"]["status"] = "lean"
        self.assertNotEqual(docs.render(status, ROOT / "README.md"),
                            docs.render(changed, ROOT / "README.md"))

    def test_links_resolve_from_both_documents(self):
        status = load_status()
        for document in docs.TARGETS:
            block = docs.render(status, document)
            targets = re.findall(r"\]\(([^)]+)\)", block)
            self.assertTrue(targets)
            for target in targets:
                with self.subTest(document=document.name, target=target):
                    self.assertTrue((document.parent / target).exists())


if __name__ == "__main__":
    unittest.main()
