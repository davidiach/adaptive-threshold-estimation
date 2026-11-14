"""Regression tests for the regenerated-record drift check."""
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_results_drift as drift  # noqa: E402
from check_results_drift import RECORDS, check, compare  # noqa: E402
import os
import tempfile

RECORD = {"config": {"k1": 0.25, "k2": 0.5}, "valid": True, "count": 3,
          "ratio": "533/183", "values": [4.281742112936694, 2.55351295663786e-15],
          "seconds": 1.8}


def encode(record, newline="\n"):
    return (json.dumps(record, indent=1) + "\n").replace("\n", newline).encode()


def run(old, new, volatile=frozenset({"seconds"})):
    files = {"committed": old, "current": new}
    return check({"record.json": volatile}, lambda _: files["committed"],
                 lambda _: files["current"])


class DriftTests(unittest.TestCase):
    def test_line_endings_and_wall_clock_are_ignored(self):
        new = dict(RECORD, seconds=2.6)
        self.assertEqual(run(encode(RECORD, "\r\n"), encode(new)), [])

    def test_last_digit_float_noise_is_accepted(self):
        new = dict(RECORD, values=[4.281742112936693, 2.6645352591003757e-15])
        self.assertEqual(run(encode(RECORD), encode(new)), [])

    def test_changed_results_are_rejected(self):
        cases = {
            "float": dict(RECORD, values=[4.2818, 2.55351295663786e-15]),
            "integer": dict(RECORD, count=4),
            "string": dict(RECORD, ratio="534/183"),
            "boolean": dict(RECORD, valid=False),
            "nested": dict(RECORD, config={"k1": 0.25, "k2": 1.0}),
            "length": dict(RECORD, values=[4.281742112936694]),
            "type": dict(RECORD, count="3"),
        }
        for name, new in cases.items():
            with self.subTest(name):
                self.assertTrue(run(encode(RECORD), encode(new)))

    def test_added_or_removed_fields_are_rejected(self):
        removed = {k: v for k, v in RECORD.items() if k != "valid"}
        self.assertTrue(run(encode(RECORD), encode(removed)))
        self.assertTrue(run(encode(RECORD), encode(dict(RECORD, extra=1))))

    def test_wall_clock_fields_are_only_ignored_where_registered(self):
        new = dict(RECORD, seconds=2.6)
        self.assertTrue(run(encode(RECORD), encode(new), volatile=frozenset()))

    def test_unreadable_or_invalid_records_fail_closed(self):
        self.assertTrue(run(encode(RECORD), b"{not json"))

        def missing(_):
            raise OSError("missing")

        self.assertTrue(check({"record.json": frozenset()}, missing, lambda _: b"{}"))

    def test_nan_matches_only_nan(self):
        self.assertEqual(compare(float("nan"), float("nan")), [])
        self.assertTrue(compare(float("nan"), 1.0))

    def test_a_record_its_check_stopped_writing_is_reported(self):
        with tempfile.TemporaryDirectory(dir=drift.ROOT) as directory:
            root = Path(directory)
            old, new = root / "old.json", root / "new.json"
            old.write_text("{}\n", encoding="utf-8")
            marker = root / "marker"
            marker.write_text("", encoding="utf-8")
            os.utime(old, (marker.stat().st_mtime - 10,) * 2)
            new.write_text("{}\n", encoding="utf-8")
            os.utime(new, (marker.stat().st_mtime + 10,) * 2)
            relative = lambda p: p.relative_to(drift.ROOT).as_posix()
            self.assertEqual(drift.stale([relative(new)], marker), [])
            self.assertEqual(len(drift.stale([relative(old)], marker)), 1)
            self.assertEqual(len(drift.stale([relative(root / "missing.json")], marker)), 1)

    def test_kept_copies_name_a_committed_record(self):
        self.assertEqual(drift.extra_pairs([".runtime/a.json=results/constants_theory.json"]),
                         {".runtime/a.json": "results/constants_theory.json"})
        for bad in ("results/constants_theory.json", "=results/x.json", "a.json=docs/x.json"):
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError):
                    drift.extra_pairs([bad])

    def test_registered_records_exist(self):
        root = Path(__file__).resolve().parents[1]
        for path in RECORDS:
            with self.subTest(path):
                self.assertTrue((root / path).is_file())


if __name__ == "__main__":
    unittest.main()
