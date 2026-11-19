"""The lock check catches a line deleted from FROZEN.sha256, which freeze.py misses."""
from pathlib import Path
import tempfile
import unittest

import freeze
import verify_locks as locks


class LockTests(unittest.TestCase):
    def test_current_locks_pass(self):
        self.assertEqual(locks.main(), 0)

    def test_deleted_or_extra_frozen_lines_are_reported(self):
        listed = list(freeze.FROZEN)
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "FROZEN.sha256"

            def write(names):
                manifest.write_text("# header\n" + "".join(f"{'0' * 64}  {n}\n" for n in names),
                                    encoding="utf-8")

            write(listed)
            self.assertEqual(locks.frozen_coverage(manifest, listed), [])
            write(listed[1:])
            self.assertIn("no longer lists " + listed[0], locks.frozen_coverage(manifest, listed)[0])
            write(listed + ["docs/extra.md"])
            self.assertIn("does not freeze", locks.frozen_coverage(manifest, listed)[0])
            write(listed + listed[:1])
            self.assertIn("twice", locks.frozen_coverage(manifest, listed)[-1])

    def test_manifests_no_lock_lists_are_pinned(self):
        # A line deleted from TIER6_FROZEN.sha256 or a published SHA256SUMS,
        # with the file it named then edited, passed every line check.
        self.assertEqual(locks.pinned_problems(), [])
        checked = ["FROZEN.sha256", *locks.TIER_LOCKS, *locks.CHECKSUM_MANIFESTS]
        listed = {name for _, name in locks.entries(locks.ROOT / "TIER6_FROZEN.sha256")}
        self.assertEqual({n for n in checked if n not in listed}, set(locks.PINNED_MANIFESTS))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lines = (locks.ROOT / "TIER6_FROZEN.sha256").read_text(encoding="utf-8").splitlines(True)
            (root / "TIER6_FROZEN.sha256").write_text("".join(lines[:-1]), encoding="utf-8")
            pinned = {"TIER6_FROZEN.sha256": locks.PINNED_MANIFESTS["TIER6_FROZEN.sha256"]}
            found = locks.pinned_problems(root, pinned, ["TIER6_FROZEN.sha256"])
            self.assertEqual(len(found), 1)
            self.assertIn("changed since its digest was pinned", found[0])
            (root / "SHA256SUMS").write_text(f"{'0' * 64}  a.txt\n", encoding="utf-8")
            found = locks.pinned_problems(root, {}, ["SHA256SUMS"])
            self.assertEqual(len(found), 1)
            self.assertIn("neither pinned", found[0])

    def test_changed_missing_or_unreadable_entries_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            (base / "a.txt").write_text("a\n", encoding="utf-8")
            good = "87428fc522803d31065e7bce3cf03fe475096631e5e07bbd7a0fde60c4cf25c7"
            manifest = base / "SHA256SUMS"
            manifest.write_text(f"{good}  a.txt\n", encoding="utf-8")
            self.assertEqual(locks.mismatches(manifest, base), [])
            (base / "a.txt").write_text("b\n", encoding="utf-8")
            self.assertEqual(len(locks.mismatches(manifest, base)), 1)
            manifest.write_text(f"{good}  missing.txt\n", encoding="utf-8")
            self.assertEqual(len(locks.mismatches(manifest, base)), 1)
            manifest.write_text("not a hash line\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "unreadable"):
                locks.entries(manifest)
            manifest.write_text("# only a comment\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "no entries"):
                locks.entries(manifest)


if __name__ == "__main__":
    unittest.main()
