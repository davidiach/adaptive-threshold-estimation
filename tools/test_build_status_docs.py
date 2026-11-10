"""Regression tests for the status summaries generated from status.json."""
import copy
import re
import sys
import tempfile
import unittest
import unittest.mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_status_docs as docs  # noqa: E402
import build_v6  # noqa: E402
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

    def test_summary_phrase_is_preferred_and_kept_out_of_the_manuscript(self):
        status = load_status()
        keys = [k for k, r in status["results"].items() if "summary" in r]
        self.assertTrue(keys)
        block = docs.render(status, ROOT / "README.md")
        for key in keys:
            result = status["results"][key]
            with self.subTest(key=key):
                phrase = docs.latex_to_markdown(result["summary"], ROOT / "README.md")
                self.assertIn("| " + docs._sentence_case(phrase) + " |", block)
                for venue in ("abstract", "boundary"):
                    self.assertNotIn(result["summary"], build_v6.status_text(status, venue))

    def test_a_status_change_changes_the_summary(self):
        status = load_status()
        changed = copy.deepcopy(status)
        current = status["results"]["psi-lower-bound"]["status"]
        changed["results"]["psi-lower-bound"]["status"] = "paper" if current == "lean" else "lean"
        self.assertNotEqual(docs.render(status, ROOT / "README.md"),
                            docs.render(changed, ROOT / "README.md"))

    def test_links_resolve_from_both_documents(self):
        status = load_status()
        for document in docs.TARGETS:
            block = docs.block_for(status, document)
            targets = re.findall(r"\]\(([^)]+)\)", block)
            self.assertTrue(targets)
            for target in targets:
                with self.subTest(document=document.name, target=target):
                    self.assertTrue((document.parent / target.split("#")[0]).exists())

    def test_landing_page_gets_counts_and_names_but_no_table(self):
        status = load_status()
        results = status["results"]
        block = docs.block_for(status, docs.SUMMARY)
        paper = [k for k in docs.ordered_keys(status) if results[k]["status"] == "paper"]
        self.assertIn(f"tracks {len(results)} results", block)
        self.assertIn(f"Lean checks {len(results) - len(paper)} of them", block)
        for key in paper:
            phrase = results[key].get("abstract") or results[key]["boundary"]
            self.assertIn(docs.latex_to_markdown(phrase, docs.SUMMARY), block)
        self.assertNotIn("\n| ", block)
        self.assertEqual(len(block.splitlines()), 3)
        # The other document still gets one row for each result.
        self.assertIn("| Result | Status | Evidence |", docs.block_for(status, docs.TABLE))

    def test_landing_page_summary_follows_the_status_source(self):
        status = load_status()
        changed = copy.deepcopy(status)
        current = status["results"]["psi-lower-bound"]["status"]
        changed["results"]["psi-lower-bound"]["status"] = "paper" if current == "lean" else "lean"
        self.assertNotEqual(docs.render_summary(status, docs.SUMMARY),
                            docs.render_summary(changed, docs.SUMMARY))
        checked = copy.deepcopy(status)
        for result in checked["results"].values():
            result["status"] = "lean"
        block = docs.render_summary(checked, docs.SUMMARY)
        self.assertIn(f"Lean checks all {len(status['results'])} results", block)
        self.assertNotIn("paper proof", block)
        single = copy.deepcopy(checked)
        single["results"]["psi-lower-bound"]["status"] = "paper"
        self.assertIn("1 has a paper proof only", docs.render_summary(single, docs.SUMMARY))

    def test_landing_page_link_reaches_the_table_heading(self):
        text = docs.TABLE.read_text(encoding="utf-8")
        self.assertIn(docs.TABLE_HEADING + "\n", text)
        self.assertLess(text.index(docs.TABLE_HEADING), text.index(docs.BEGIN))
        self.assertEqual(docs.TABLE_ANCHOR, docs.TABLE_HEADING[3:].lower().replace(" ", "-"))
        self.assertIn("#" + docs.TABLE_ANCHOR, docs.render_summary(load_status(), docs.SUMMARY))

    def test_table_document_without_its_heading_fails(self):
        status = load_status()
        with tempfile.TemporaryDirectory() as tmp:
            document = Path(tmp) / "RESULTS.md"
            document.write_text(f"intro\n{docs.BEGIN}\nold\n{docs.END}\n", encoding="utf-8")
            with unittest.mock.patch.object(docs, "TABLE", document):
                with self.assertRaisesRegex(ValueError, "needs the heading"):
                    docs.update(status, (document,), write=False)


if __name__ == "__main__":
    unittest.main()
