"""Regression tests for the trust-anchor guard (check_trust_anchors.py)."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

import check_trust_anchors as guard

H1, H2 = "a" * 64, "b" * 64

AUDIT = '''"""Audit X."""
import re
from verify_shared import FORBIDDEN

SPEC_HASH = "{spec}"
TARGETS = {{"x_lower": "LowerStatement", "x_upper": "UpperStatement"}}
EXACT_COUNT = {count}
EXACT = """
{exact}
"""


def audit(source: str) -> bool:
    """Reject proof escapes."""
    {body}
'''
STATEMENT_A = "example : ∀ n : ℕ, n ≤ n + 1 :=\n  X.a"
STATEMENT_B = "example : ∀ n : ℕ, n < n + 2 :=\n  X.b"
WORKFLOW = """name: Checks
on: [pull_request]
jobs:
  audit:
    runs-on: ubuntu-latest
    timeout-minutes: {timeout}
    steps:
      - name: {step}
        run: python tools/verify_x.py --replay
      - name: Other
        run: python tools/verify_y.py{tail}
"""


def audit_source(spec=H1, count=1, exact=STATEMENT_A, body="return not FORBIDDEN.search(source)",
                 targets=None):
    text = AUDIT.format(spec=spec, count=count, exact=exact, body=body)
    if targets is not None:
        text = text.replace('{"x_lower": "LowerStatement", "x_upper": "UpperStatement"}', targets)
    return text


class Repo:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.git("init", "-q", "-b", "main")

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), "-c", "user.name=test",
                               "-c", "user.email=test@example.invalid", *args],
                              check=True, capture_output=True, text=True).stdout.strip()

    def commit(self, files: dict[str, str | None], message: str = "change") -> str:
        for path, text in files.items():
            target = self.root / path
            if text is None:
                target.unlink()
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")


class GuardTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Repo(Path(self.tmp.name))
        self.git = guard.Git(self.tmp.name)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def anchors(self, before: dict, after: dict) -> list[guard.Anchor]:
        base = self.repo.commit(before, "base")
        head = self.repo.commit(after, "head")
        return guard.changed_anchors(self.git, base, head)

    def run_guard(self, base: str, head: str) -> tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = guard.main(["--repo", self.tmp.name, "--base", base, "--head", head])
        return code, out.getvalue()

    def kinds(self, anchors) -> list[tuple[str, str]]:
        return sorted((a.kind, a.name) for a in anchors)

    # -- what counts as a change ------------------------------------------

    def test_changed_pin_is_flagged(self):
        found = self.anchors({"tools/verify_x.py": audit_source()},
                             {"tools/verify_x.py": audit_source(spec=H2)})
        self.assertEqual(self.kinds(found), [("pin", "SPEC_HASH")])

    def test_added_statement_passes_and_changed_statement_is_flagged(self):
        both = STATEMENT_A + "\n\n" + STATEMENT_B
        self.assertEqual(self.anchors({"tools/verify_x.py": audit_source()},
                                      {"tools/verify_x.py": audit_source(count=2, exact=both)}), [])
        weaker = STATEMENT_A.replace("n ≤ n + 1", "n ≤ n + 2") + "\n\n" + STATEMENT_B
        found = self.anchors({}, {"tools/verify_x.py": audit_source(count=2, exact=weaker)})
        self.assertEqual(self.kinds(found), [("statement", "EXACT:X.a")])

    def test_reformatted_statement_passes(self):
        reflowed = "example :\n    ∀ n : ℕ,   n ≤ n + 1 := X.a"
        self.assertEqual(self.anchors({"tools/verify_x.py": audit_source()},
                                      {"tools/verify_x.py": audit_source(exact=reflowed)}), [])

    def test_removed_target_mapping_is_flagged(self):
        found = self.anchors({"tools/verify_x.py": audit_source()},
                             {"tools/verify_x.py": audit_source(targets='{"x_lower": "LowerStatement"}')})
        self.assertEqual(self.kinds(found), [("statement", "TARGETS['x_upper']")])

    def test_count_counts_only_when_it_falls(self):
        self.assertEqual(self.anchors({"tools/verify_x.py": audit_source(count=3)},
                                      {"tools/verify_x.py": audit_source(count=4)}), [])
        found = self.anchors({}, {"tools/verify_x.py": audit_source(count=2)})
        self.assertEqual(self.kinds(found), [("statement", "EXACT_COUNT")])

    def test_comments_and_docstrings_are_ignored_but_code_is_not(self):
        noted = audit_source().replace('"""Reject proof escapes."""', '"""Reject escapes."""  # note')
        self.assertEqual(self.anchors({"tools/verify_x.py": audit_source()},
                                      {"tools/verify_x.py": noted}), [])
        found = self.anchors({}, {"tools/verify_x.py": audit_source(body="return True")})
        self.assertEqual(self.kinds(found), [("code", "audit")])

    def test_changed_import_of_the_shared_guard_is_flagged(self):
        local = audit_source().replace("from verify_shared import FORBIDDEN",
                                       "FORBIDDEN = re.compile('sorry')")
        found = self.anchors({"tools/verify_x.py": audit_source()}, {"tools/verify_x.py": local})
        self.assertIn(("code", "import verify_shared.FORBIDDEN"), self.kinds(found))

    def test_names_in_a_verifier_list_compare_one_by_one(self):
        def selector(names):
            return f'VERIFIERS = {{"kernel": """\n    {names}\n"""}}\n'
        self.assertEqual(self.anchors({".github/lean_ci.py": selector("sharp_rms upper_scale")},
                                      {".github/lean_ci.py": selector("sharp_rms upper_scale tier6")}),
                         [])
        found = self.anchors({}, {".github/lean_ci.py": selector("sharp_rms tier6")})
        self.assertEqual(self.kinds(found), [("code", "VERIFIERS['kernel' upper_scale]")])

    def test_lock_entries_changed_or_removed_are_flagged(self):
        lock = {"definitions": {"X.a": "1:2", "X.b": "3:4"}, "added": [{"count": 2}]}
        grown = {"definitions": {"X.a": "1:2", "X.b": "3:4", "X.c": "5:6"},
                 "added": [{"count": 2}, {"count": 1}]}
        self.assertEqual(self.anchors({"tools/definition_lock.json": json.dumps(lock)},
                                      {"tools/definition_lock.json": json.dumps(grown)}), [])
        changed = dict(grown, definitions={"X.a": "1:9", "X.c": "5:6"})
        found = self.anchors({}, {"tools/definition_lock.json": json.dumps(changed)})
        self.assertEqual(self.kinds(found), [("lock", "definitions/X.a"), ("lock", "definitions/X.b")])

    def test_manifest_digest_change_is_a_pin(self):
        found = self.anchors({"FROZEN.sha256": f"{H1}  lean/A.lean\n{H1}  tools/x.py\n"},
                             {"FROZEN.sha256": f"{H2}  lean/A.lean\n{H1}  tools/x.py\n"})
        self.assertEqual(self.kinds(found), [("pin", "lean/A.lean")])

    def test_workflow_removals_and_escapes_are_flagged_labels_are_not(self):
        base = WORKFLOW.format(timeout=60, step="Audit X", tail="")
        relabelled = WORKFLOW.format(timeout=90, step="Audit X and its replay", tail="")
        self.assertEqual(self.anchors({".github/workflows/checks.yml": base},
                                      {".github/workflows/checks.yml": relabelled}), [])
        weakened = relabelled.replace(" --replay", "").replace("verify_y.py", "verify_y.py || true")
        found = self.anchors({}, {".github/workflows/checks.yml": weakened})
        self.assertEqual(sorted(a.detail.split(":")[0] for a in found), ["added", "removed", "removed"])
        skipped = relabelled.replace("      - name: Other\n", "      - name: Other\n        if: false\n")
        found = self.anchors({".github/workflows/checks.yml": relabelled},
                             {".github/workflows/checks.yml": skipped})
        self.assertEqual([a.detail for a in found], ["added: if: false"])

    def test_lean_statement_files(self):
        spec = "def LowerStatement : Prop := True\n"
        found = self.anchors({"lean/ThresholdHC/X/Specification.lean": spec},
                             {"lean/ThresholdHC/X/Specification.lean": spec.replace("True", "False")})
        self.assertEqual(self.kinds(found), [("statement", "<file>")])
        self.assertEqual(self.anchors({}, {"lean/ThresholdHC/Y/Specification.lean": spec,
                                           "lean/ThresholdHC/X/Proof.lean": "-- proof\n"}), [])

    def test_out_of_scope_files_are_ignored(self):
        before = {"results/r.json": json.dumps({"digest": H1}), "tools/test_verify_x.py": "x = 1\n",
                  "tools/build_v6.py": "def f():\n    return 1\n"}
        after = {"results/r.json": json.dumps({"digest": H2}), "tools/test_verify_x.py": "x = 2\n",
                 "tools/build_v6.py": "def f():\n    return 2\n"}
        self.assertEqual(self.anchors(before, after), [])

    def test_deleted_checker_is_one_anchor(self):
        found = self.anchors({"tools/verify_x.py": audit_source()}, {"tools/verify_x.py": None})
        self.assertEqual(self.kinds(found), [("code", "<deleted file>")])

    def test_unparseable_new_version_is_flagged(self):
        found = self.anchors({"tools/verify_x.py": audit_source()},
                             {"tools/verify_x.py": "def broken(:\n"})
        self.assertEqual(self.kinds(found), [("code", "<unreadable>")])

    def test_removed_log_line_is_flagged(self):
        found = self.anchors({guard.LEDGER: "# Log\n\n## Entry\n\n- Why: a reason\n"},
                             {guard.LEDGER: "# Log\n"})
        self.assertEqual({a.kind for a in found}, {"log"})

    def test_key_names_the_old_content(self):
        one = guard.Anchor("pin", "tools/x.py", "SPEC_HASH", f'SPEC_HASH = "{H1}"', "")
        two = guard.Anchor("pin", "tools/x.py", "SPEC_HASH", f'SPEC_HASH = "{H2}"', "")
        self.assertTrue(one.key.startswith("pin tools/x.py SPEC_HASH@"))
        self.assertNotEqual(one.key, two.key)

    # -- acknowledgement and the verdict ------------------------------------

    def changed_pin(self) -> tuple[str, str, str]:
        base = self.repo.commit({"tools/verify_x.py": audit_source()}, "base")
        head = self.repo.commit({"tools/verify_x.py": audit_source(spec=H2)}, "head")
        (anchor,) = guard.changed_anchors(self.git, base, head)
        return base, head, anchor.key

    def test_unacknowledged_change_fails_and_prints_the_lines_to_add(self):
        base, head, key = self.changed_pin()
        code, output = self.run_guard(base, head)
        self.assertEqual(code, 1)
        self.assertIn(f"  - `{key}`", output)

    def test_acknowledgement_with_a_reason_passes(self):
        base, _, key = self.changed_pin()
        head = self.repo.commit({guard.LEDGER: f"# Log\n\n## Spec fix\n\n- Why: typo in X.\n- `{key}`\n"})
        self.assertEqual(self.run_guard(base, head)[0], 0)

    def test_acknowledgement_needs_a_reason(self):
        base, _, key = self.changed_pin()
        head = self.repo.commit({guard.LEDGER: f"# Log\n\n## Spec fix\n\n- `{key}`\n"})
        code, output = self.run_guard(base, head)
        self.assertEqual(code, 1)
        self.assertIn("has no `- Why:` line", output)

    def test_acknowledgement_must_be_added_by_the_change(self):
        source = audit_source()
        anchor = guard.Anchor("pin", "tools/verify_x.py", "SPEC_HASH",
                              guard.python_items(source)["SPEC_HASH"][1], "")
        base = self.repo.commit({"tools/verify_x.py": source,
                                 guard.LEDGER: f"# Log\n\n## Old\n\n- Why: earlier.\n- `{anchor.key}`\n"})
        head = self.repo.commit({"tools/verify_x.py": audit_source(spec=H2)})
        self.assertEqual(self.run_guard(base, head)[0], 1)

    def test_acknowledgement_in_a_code_block_does_not_count(self):
        base, _, key = self.changed_pin()
        head = self.repo.commit({guard.LEDGER: f"# Log\n\n- Why: x\n\n```\n- `{key}`\n```\n"})
        self.assertEqual(self.run_guard(base, head)[0], 1)

    def test_changes_on_the_base_branch_are_not_counted(self):
        fork = self.repo.commit({"tools/verify_x.py": audit_source(), "lean/A.lean": "-- a\n"})
        main = self.repo.commit({"tools/verify_x.py": audit_source(spec=H2)}, "main moves on")
        self.repo.git("checkout", "-q", "-b", "topic", fork)
        topic = self.repo.commit({"lean/A.lean": "-- b\n"}, "topic")
        code, output = self.run_guard(main, topic)
        self.assertEqual(code, 0, output)

    def test_unknown_revision_is_a_fault(self):
        base = self.repo.commit({"tools/verify_x.py": audit_source()})
        code, output = self.run_guard(base, "f" * 40)
        self.assertEqual(code, 3)
        self.assertIn("FAULT", output)

    def test_files_are_read_never_run(self):
        marker = Path(self.tmp.name) / "ran"
        hostile = textwrap.dedent(f"""
            from pathlib import Path
            Path({str(marker)!r}).write_text("ran")
            SPEC_HASH = "{H2}"
        """)
        base = self.repo.commit({"tools/verify_x.py": audit_source()})
        head = self.repo.commit({"tools/verify_x.py": hostile})
        self.assertEqual(self.run_guard(base, head)[0], 1)
        self.assertFalse(marker.exists())


if __name__ == "__main__":
    unittest.main()
