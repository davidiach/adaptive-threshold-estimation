"""The project-wide Lean source guard covers what the frozen Tier patterns miss."""
from pathlib import Path
import tempfile
import unittest

import verify_lean_sources as guard
from verify_tier6 import FORBIDDEN as TIER6_FORBIDDEN, strip_comments


class LeanSourceGuardTests(unittest.TestCase):
    def test_current_sources_pass_and_include_unfrozen_tier_modules(self):
        paths = guard.sources()
        self.assertEqual(guard.violations(paths), [])
        names = {p.relative_to(guard.ROOT).as_posix() for p in paths}
        self.assertIn("lean/ThresholdHC/Tier6/Full.lean", names)
        self.assertIn("proposals/constants/UniformArithmetic.lean", names)
        self.assertFalse(any("/.lake/" in name or "/.audit/" in name for name in names))

    def test_escapes_missed_by_the_frozen_tier_pattern_are_rejected(self):
        hidden = "set_option debug.skipKernelTC true\ntheorem hidden : False := by sorry\n"
        sources = {
            "admit.lean": "theorem t : 1 = 2 := by admit\n",
            "string.lean": 'def a : String := "/-"\n' + hidden + 'def b : String := "-/"\n',
            "escaped.lean": "def \u00ab/-\u00bb : Nat := 0\n" + hidden + "def \u00ab-/\u00bb : Nat := 0\n",
            "guard.lean": "#guard_msgs (drop all) in\nexample : 1 = 2 := by stop rfl\n",
            "doc.lean": "/--/ -- -/ axiom bad : False\ntheorem t : 1 = 2 := bad.elim\n",
        }
        with tempfile.TemporaryDirectory() as directory:
            paths = []
            for name, text in sources.items():
                path = Path(directory) / name
                path.write_text(text, encoding="utf-8")
                paths.append(path)
                if name != "guard.lean":
                    self.assertIsNone(TIER6_FORBIDDEN.search(strip_comments(text)), name)
            found = guard.violations(paths)
        self.assertEqual(len(found), 5, found)

    def test_compiled_code_numeral_keywords_and_instance_overrides_are_rejected(self):
        # Each of these elaborates in Lean 4.36, and the frozen pattern misses it.
        sources = {
            "native.lean": "example : 2 + 2 = 4 := by decide (native := true)\n",
            "config.lean": "example : 2 + 2 = 4 := by decide (config := { native := true })\n",
            # Lean ends the numeral at the letter, so this declares an axiom.
            "numeral.lean": "def x : Nat := 1axiom bad : False\n",
            "scoped.lean": "scoped instance hijack : LE Nat := ⟨fun _ _ => True⟩\n",
            "priority.lean": "instance (priority := high) hijack : LE Nat := ⟨fun _ _ => True⟩\n",
            "attribute.lean": "attribute [scoped instance] Nat.instLE\n",
        }
        with tempfile.TemporaryDirectory() as directory:
            paths = []
            for name, text in sources.items():
                path = Path(directory) / name
                path.write_text(text, encoding="utf-8")
                paths.append(path)
                self.assertIsNone(TIER6_FORBIDDEN.search(strip_comments(text)), name)
            found = guard.violations(paths)
        self.assertEqual(len(found), len(sources), found)

    def test_ordinary_words_are_not_mistaken_for_escapes(self):
        sources = {"words.lean": "open scoped ENNReal\ndef stop_x (hρ1 : 1 ≤ 2) : Nat := 0\n"
                                 "-- an Alternative and nativeish name in a comment\n"
                                 "def selectedAlternative : Nat := 1\n"}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "words.lean"
            path.write_text(sources["words.lean"], encoding="utf-8")
            self.assertEqual(guard.violations([path]), [])

    def test_unclosed_comment_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "open.lean"
            path.write_text("/- never closed\ntheorem t : True := trivial\n", encoding="utf-8")
            self.assertEqual(len(guard.violations([path])), 1)


if __name__ == "__main__":
    unittest.main()
