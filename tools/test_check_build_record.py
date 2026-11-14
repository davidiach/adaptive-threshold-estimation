"""Regression tests for the current v6 build-record check."""
import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_build_record as check  # noqa: E402


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class BuildRecordTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.pdf = self.dir / "build.pdf"
        self.pdf.write_bytes(b"%PDF-1.5 example")
        (self.dir / "a.tex").write_text("A\n", encoding="utf-8")
        (self.dir / "status.json").write_text("{}\n", encoding="utf-8")
        self.record = {
            "pages": 10, "pdf_sha256": sha(self.pdf.read_bytes()), "pdf_bytes": 16,
            "tex_sources": {"a.tex": sha(b"A\n")}, "source_commit": "abc",
            "status_manifest_sha256": sha(b"{}\n"),
            "changed_pages": [1, 6, 7], "visual_pages_checked": [1, 2, 6, 7],
            "relocated_pages": {"9": 8},
        }

    def tearDown(self):
        self.tmp.cleanup()

    def errors(self, mutate=lambda r: None, pages=10):
        record = copy.deepcopy(self.record)
        mutate(record)
        return check.record_errors(record, self.pdf, pages)

    def test_a_consistent_record_passes(self):
        self.assertEqual(self.errors(), [])
        self.assertEqual(self.errors(pages=None), [])

    def test_the_record_must_describe_its_own_pdf(self):
        cases = {
            "hash": lambda r: r.__setitem__("pdf_sha256", "0" * 64),
            "size": lambda r: r.__setitem__("pdf_bytes", 17),
            "field": lambda r: r.pop("source_commit"),
            "status hash": lambda r: r.pop("status_manifest_sha256"),
            "unchecked change": lambda r: r["visual_pages_checked"].remove(7),
            "unrecorded visual check": lambda r: r.pop("visual_pages_checked"),
            "page range": lambda r: r["changed_pages"].append(11),
            "relocation": lambda r: r["relocated_pages"].__setitem__("x", 2),
        }
        for name, mutate in cases.items():
            with self.subTest(name):
                self.assertTrue(self.errors(mutate))
        self.assertTrue(self.errors(pages=11))

    def test_the_older_status_key_is_accepted(self):
        def rename(r): r["status_source_sha256"] = r.pop("status_manifest_sha256")
        self.assertEqual(self.errors(rename), [])

    def test_staleness_names_each_changed_source(self):
        self.assertEqual(check.staleness(self.record, self.dir), [])
        (self.dir / "a.tex").write_text("B\n", encoding="utf-8")
        (self.dir / "b.tex").write_text("new\n", encoding="utf-8")
        (self.dir / "status.json").write_text('{"x": 1}\n', encoding="utf-8")
        notes = check.staleness(self.record, self.dir)
        self.assertEqual(len(notes), 3)
        self.assertTrue(any("a.tex changed" in n for n in notes))
        self.assertTrue(any("b.tex is new" in n for n in notes))
        self.assertTrue(any("status.json" in n for n in notes))

    def test_link_line_is_required(self):
        readme = self.dir / "README.md"
        readme.write_text("[Current manuscript](builds/x.pdf) · [Build record](builds/x.json)\n",
                          encoding="utf-8")
        self.assertEqual(check.current_links(readme),
                         (self.dir / "builds/x.pdf", self.dir / "builds/x.json"))
        readme.write_text("No links here.\n", encoding="utf-8")
        with self.assertRaises(ValueError):
            check.current_links(readme)

    def test_the_repository_record_describes_its_pdf(self):
        pdf, record = check.current_links()
        self.assertEqual(check.record_errors(json.loads(record.read_text(encoding="utf-8")),
                                             pdf, None), [])


if __name__ == "__main__":
    unittest.main()
