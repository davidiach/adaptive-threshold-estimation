"""Require every change to the checks' own trust anchors to be acknowledged.

A pull request can change a proof and, in the same diff, the audit that judges
it: the digest that pins a specification, a restated statement, an entry of a
lock, the shared proof-escape guard, or the CI line that runs an audit. Each
such edit can be right, but none should pass unnoticed. This guard compares two
commits and lists every trust anchor that the newer one changes or removes:

  pin        a pinned SHA-256 digest in checker code or lock data;
  statement  a restated Lean statement or target mapping in an audit script, or
             a Lean specification, target or audit file;
  lock       an entry of a lock or manifest (the definition lock, specification
             freezes, the FROZEN manifests, the toolchain and Mathlib pins);
  code       a top-level definition of checker code (the verify_, check_
             and lock scripts, freeze.py, score.py and run_real_guarded.py in
             tools/, and the Python files in .github/; tests excluded), an
             entry removed from a list of names it checks, or a deleted file;
  ci         a command removed from a workflow, or an added line that skips a
             step or lets a failing one pass;
  log        a line removed from the checker-change log.

Additions are not listed: a new pin, restated statement, lock entry, name or
audit adds checks, and a `*_COUNT` constant counts only when it falls. Comments,
docstrings and workflow step names and timeouts are ignored. Published evidence (results/,
research/, paper/, inputs/) is out of scope; the locks protect it.

Every listed change must be acknowledged in the checker-change log, LEDGER
below, by a line that the same diff adds, under an entry with a `- Why:` line.
The guard prints the lines to add. The two commits are compared from their
merge base, so changes that reached the base branch separately are not counted.

The guard reads both commits through git as data. It never imports or runs code
from either one, so CI can run the base branch's copy of this file against a
pull request: the author of a change cannot edit the guard that judges it. The
guard uses only the standard library; run it with `python -I`.

Exit 0: nothing to acknowledge, or everything acknowledged. Exit 1: changes
that still need acknowledgement. Exit 3: the guard could not run (a git error,
a base file that does not parse); a fault says nothing about the change.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

LEDGER = "docs/process/CHECKER_CHANGES.md"
PRESERVED = ("results/", "research/", "paper/", "inputs/")
PINS = ("lean/lean-toolchain", "lean/lakefile.toml")
HEX64 = re.compile(r"(?<![0-9A-Fa-f])[0-9a-f]{64}(?![0-9A-Fa-f])")
CHECKER = re.compile(r"tools/(?:verify_\w+|check_\w+|\w+_lock|freeze|score|run_real_guarded)\.py"
                     r"|\.github/(?!test_)\w+\.py")
# Module-level constants whose elements are statements or target mappings.
STATEMENT_NAME = re.compile(r"EXACT|TARGET|STATEMENT|COMPONENT")
# A string of names, such as a list of verifiers, compared name by name.
WORDS = re.compile(r"[\w.*?\[\]/-]+")
EXAMPLE_START = re.compile(r"(?m)^(?=[ \t]*example\b)")
THEOREM_AT_END = re.compile(r":=\s*@?(\S+)\s*$")
LEAN_STATEMENT = re.compile(r"(?:Specification|Statements?\d*|Targets?|Audit|\w+Spec|\w+Target)\.lean")
# An added workflow line that skips a step or lets a failing one pass.
CI_ESCAPE = re.compile(r"^-?\s*if:|continue-on-error|\|\|\s*(?:true|:|exit\s+0)\b")
# Workflow lines that do not change what is checked.
CI_LABEL = re.compile(r"^-?\s*(?:name|timeout-minutes):")
# A key as report() prints it, in backticks; other backticked text is prose.
KEY = re.compile(r"`((?:pin|statement|lock|code|ci|log) [^`\n]+@[0-9a-f]{12})`")
WHY = re.compile(r"^\s*-\s*Why:\s*\S")


class Fault(Exception):
    """The guard could not judge the change."""


@dataclass(frozen=True)
class Anchor:
    kind: str
    path: str
    name: str
    content: str  # what changed: the old content, or the new line for an added escape
    detail: str

    @property
    def key(self) -> str:
        digest = hashlib.sha256(self.content.encode("utf-8", "surrogateescape")).hexdigest()
        name = " ".join(self.name.split()).replace("`", "'")
        return f"{self.kind} {self.path} {name}@{digest[:12]}"


class Git:
    def __init__(self, repo: str) -> None:
        self.repo = repo

    def run(self, *args: str) -> bytes:
        try:
            done = subprocess.run(["git", "-C", self.repo, *args], capture_output=True, timeout=300)
        except (OSError, subprocess.TimeoutExpired) as error:
            raise Fault(f"git {args[0]} could not run: {error}") from error
        if done.returncode:
            message = done.stderr.decode("utf-8", "replace").strip()
            raise Fault(f"git {' '.join(args)} failed: {message}")
        return done.stdout

    def commit(self, rev: str) -> str:
        return self.run("rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}").decode().strip()

    def merge_base(self, base: str, head: str) -> str:
        return self.run("merge-base", base, head).decode().strip()

    def changed(self, base: str, head: str) -> list[tuple[str, str]]:
        raw = self.run("diff", "--name-status", "--no-renames", "-z", base, head, "--")
        fields = raw.decode("utf-8", "surrogateescape").split("\0")
        return [(fields[i][0], fields[i + 1]) for i in range(0, len(fields) - 1, 2)]

    def text(self, rev: str, path: str) -> str | None:
        exists = subprocess.run(["git", "-C", self.repo, "cat-file", "-e", f"{rev}:{path}"],
                                capture_output=True)
        if exists.returncode:
            return None
        return self.run("show", f"{rev}:{path}").decode("utf-8", "surrogateescape")


def category(path: str) -> str | None:
    name = path.rsplit("/", 1)[-1]
    if path == LEDGER:
        return "ledger"
    if path.startswith(PRESERVED):
        return None
    if CHECKER.fullmatch(path):
        return "python"
    if re.fullmatch(r"\.github/workflows/[^/]+\.ya?ml", path):
        return "workflow"
    if path.endswith(".json") and (path.startswith("tools/") or path == "lean/lake-manifest.json"
                                   or (path.startswith("lean/") and re.search(r"(?i)spec|lock|freeze", name))):
        return "json"
    if path.endswith(".sha256") or path in PINS:
        return "lines"
    if path.startswith("lean/") and LEAN_STATEMENT.fullmatch(name):
        return "lean"
    return None


def first_line(text: str, limit: int = 100) -> str:
    line = next((part.strip() for part in text.splitlines() if part.strip()), "")
    line = line.replace("`", "'")
    return line if len(line) <= limit else line[:limit - 3] + "..."


def short(text: str, limit: int = 60) -> str:
    text = " ".join(text.split()).replace("`", "'")
    return text if len(text) <= limit else text[:limit - 3] + "..."


# ---- Python checker code -------------------------------------------------

def _strip_docstrings(node: ast.AST) -> ast.AST:
    for child in ast.walk(node):
        body = getattr(child, "body", None)
        if (isinstance(child, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
                and body and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str)):
            child.body = body[1:] or [ast.Pass()]
    return node


def _dump(node: ast.AST) -> str:
    return ast.dump(node, include_attributes=False)


def _literal_elements(value: ast.AST) -> list[tuple[str, str]] | None:
    """(name, content) for each element of a literal collection of constants.

    A dictionary value that is a string of several names, such as the verifier
    list of a CI job, contributes one element per name."""
    if isinstance(value, ast.Dict) and all(isinstance(k, ast.Constant) for k in value.keys):
        if all(isinstance(v, ast.Constant) for v in value.values):
            elements = []
            for k, v in zip(value.keys, value.values):
                words = v.value.split() if isinstance(v.value, str) else []
                if len(words) > 1 and all(WORDS.fullmatch(w) for w in words):
                    elements += [(f"{k.value!r} {w}", f"{k.value!r}: {w}") for w in words]
                else:
                    elements.append((repr(k.value), f"{k.value!r}: {v.value!r}"))
            return elements
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)) and value.elts:
        if all(isinstance(e, ast.Constant) for e in value.elts):
            return [(repr(e.value), repr(e.value)) for e in value.elts]
    return None


def _statement_chunks(text: str) -> list[tuple[str, str]]:
    chunks = []
    for chunk in EXAMPLE_START.split(text):
        normal = " ".join(chunk.split())
        if not normal:
            continue
        if normal.startswith("example"):
            match = THEOREM_AT_END.search(normal)
            chunks.append((match.group(1) if match else short(normal, 40), normal))
        else:
            chunks.append(("<text>", normal))
    return chunks


def python_items(source: str) -> dict[str, tuple[str, str, str]]:
    """name -> (kind, content, detail) for each top-level item of a checker module."""
    tree = _strip_docstrings(ast.parse(source))
    items: dict[str, tuple[str, str, str]] = {}

    def put(name: str, kind: str, content: str, detail: str) -> None:
        if name in items:
            old_kind, old_content, old_detail = items[name]
            content = old_content + "\n" + content
            kind = old_kind if old_kind != "code" else kind
            detail = old_detail
        items[name] = (kind, content, detail)

    for node in tree.body:
        segment = ast.get_source_segment(source, node) or ""
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            put(node.name, "code", _dump(node), first_line(segment))
        elif isinstance(node, (ast.Assign, ast.AnnAssign)) and node.value is not None:
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if not all(isinstance(t, ast.Name) for t in targets):
                put(f"<statement {short(segment, 40)}>", "code", _dump(node), first_line(segment))
                continue
            var = ",".join(t.id for t in targets)
            named = bool(STATEMENT_NAME.search(var))
            value = node.value
            if isinstance(value, ast.Constant) and isinstance(value.value, str) and "example" in value.value:
                for theorem, chunk in _statement_chunks(value.value):
                    put(f"{var}:{theorem}", "statement", chunk, first_line(chunk))
                continue
            elements = _literal_elements(value)
            if elements is not None:
                for name, content in elements:
                    kind = "pin" if HEX64.search(content) else "statement" if named else "code"
                    put(f"{var}[{short(name, 50)}]", kind, content, f"{var}[{short(name, 50)}]")
                continue
            if (var.endswith("_COUNT") and isinstance(value, ast.Constant)
                    and isinstance(value.value, int)):
                put(var, "count", str(value.value), first_line(segment))
                continue
            kind = "pin" if HEX64.search(segment) else "statement" if named else "code"
            put(var, kind, _dump(node), first_line(segment))
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            module = getattr(node, "module", None) or ""
            for alias in node.names:
                name = f"import {module + '.' if module else ''}{alias.name}"
                put(name, "code", f"{name} as {alias.asname}", name)
        elif isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant):
            continue  # a bare string or constant has no effect
        else:
            dump = _dump(node)
            digest = hashlib.sha256(dump.encode()).hexdigest()[:8]
            put(f"<statement {digest}>", "code", dump, first_line(segment))
    return items


# ---- data and text files -------------------------------------------------

def json_items(text: str) -> dict[str, tuple[str, str, str]]:
    items: dict[str, tuple[str, str, str]] = {}

    def walk(value, path: list[str]) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                walk(child, path + [str(key)])
        elif isinstance(value, list):
            for index, child in enumerate(value):
                walk(child, path + [str(index)])
        else:
            content = json.dumps(value, sort_keys=True, ensure_ascii=False)
            name = "/".join(path) or "<root>"
            kind = "pin" if HEX64.search(content) else "lock"
            items[short(name, 120)] = (kind, content, f"{short(name, 80)} = {short(content, 40)}")

    walk(json.loads(text), [])
    return items


def line_items(text: str) -> dict[str, tuple[str, str, str]]:
    items: dict[str, tuple[str, str, str]] = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        manifest = re.fullmatch(r"([0-9a-f]{64})\s+\*?(.+)", line)
        if manifest:
            items[manifest.group(2)] = ("pin", line, manifest.group(2))
        else:
            items[short(line, 80)] = ("lock", line, short(line, 80))
    return items


def _lines(text: str) -> Counter:
    lines = (" ".join(line.split()) for line in text.splitlines())
    return Counter(line for line in lines
                   if line and not line.startswith("#") and not CI_LABEL.match(line))


def workflow_anchors(path: str, old: str, new: str) -> list[Anchor]:
    before, after = _lines(old), _lines(new)
    found = []
    for line, count in sorted((before - after).items()):
        found.append(Anchor("ci", path, short(line), line, f"removed: {short(line, 90)}"
                            + (f" ({count} of {before[line]})" if before[line] > 1 else "")))
    for line in sorted(after - before):
        if CI_ESCAPE.search(line):
            found.append(Anchor("ci", path, short(line), line, f"added: {short(line, 90)}"))
    return found


def ledger_anchors(path: str, old: str, new: str) -> list[Anchor]:
    removed = Counter(old.splitlines()) - Counter(new.splitlines())
    return [Anchor("log", path, short(line) or "<blank line>", line, f"removed: {short(line, 90)}")
            for line in sorted(removed) if line.strip()]


def compare(path: str, kind_of_file: str, old: str, new: str | None) -> list[Anchor]:
    deleted_kind = {"python": "code", "workflow": "ci", "json": "lock", "lines": "lock",
                    "lean": "statement", "ledger": "log"}[kind_of_file]
    if new is None:
        return [Anchor(deleted_kind, path, "<deleted file>", old, "the file was deleted")]
    if kind_of_file == "lean":
        if old.replace("\r\n", "\n") == new.replace("\r\n", "\n"):
            return []
        return [Anchor("statement", path, "<file>", old, "the statement file changed")]
    if kind_of_file == "workflow":
        return workflow_anchors(path, old, new)
    if kind_of_file == "ledger":
        return ledger_anchors(path, old, new)
    reader = {"python": python_items, "json": json_items, "lines": line_items}[kind_of_file]
    try:
        before = reader(old)
    except (SyntaxError, ValueError, RecursionError) as error:
        raise Fault(f"the base version of {path} cannot be read: {error}") from error
    try:
        after = reader(new)
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        return [Anchor(deleted_kind, path, "<unreadable>", old, "the new version cannot be parsed")]
    found = []
    for name, (kind, content, detail) in before.items():
        if kind == "count":
            kind = "statement" if STATEMENT_NAME.search(name) else "code"
            if name in after and after[name][0] == "count" and int(after[name][1]) >= int(content):
                continue
        if name not in after:
            found.append(Anchor(kind, path, name, content, f"removed: {detail}"))
        elif after[name][1] != content:
            found.append(Anchor(kind, path, name, content, f"changed: {detail}"))
    return found


def changed_anchors(git: Git, base: str, head: str) -> list[Anchor]:
    found = []
    for status, path in git.changed(base, head):
        kind_of_file = category(path)
        if kind_of_file is None or status == "A":
            continue
        old = git.text(base, path)
        if old is None:
            continue
        found.extend(compare(path, kind_of_file, old, git.text(head, path)))
    return found


# ---- the checker-change log ----------------------------------------------

def acknowledgements(old: str | None, new: str | None) -> tuple[set[str], set[str]]:
    """Keys in lines this change adds to the log: (with a reason, without one)."""
    if not new:
        return set(), set()
    added = Counter(new.splitlines()) - Counter((old or "").splitlines())
    sections: list[list[str]] = [[]]
    fenced = False
    for line in new.splitlines():
        if line.lstrip().startswith("```"):
            fenced = not fenced
            continue
        if fenced:
            continue
        if line.startswith("## "):
            sections.append([])
        sections[-1].append(line)
    explained, unexplained = set(), set()
    for section in sections:
        reason = any(WHY.match(line) for line in section)
        for line in section:
            if added[line] <= 0:
                continue
            added[line] -= 1
            for key in KEY.findall(line):
                (explained if reason else unexplained).add(key.strip())
    return explained, unexplained


# ---- report ---------------------------------------------------------------

def report(anchors: list[Anchor], explained: set[str], unexplained: set[str],
           base: str, head: str) -> tuple[str, int]:
    pending = [a for a in anchors if a.key not in explained]
    keys = {a.key for a in anchors}
    lines = [f"Trust anchors changed between {base[:12]} (merge base) and {head[:12]}: "
             f"{len(anchors)}; acknowledged: {len(anchors) - len(pending)}; "
             f"still to acknowledge: {len(pending)}."]
    if anchors:
        lines.append("")
        for a in anchors:
            mark = "ok " if a.key in explained else "-- "
            lines.append(f"{mark}{a.kind:9} {a.path}: {a.detail}")
    stray = sorted((explained | unexplained) - keys)
    if stray:
        lines += ["", "Acknowledged in the log but not changed here (check the key):"]
        lines += [f"   `{key}`" for key in stray]
    if pending:
        missing_reason = [a for a in pending if a.key in unexplained]
        if missing_reason:
            lines += ["", "These keys are in the log, but their entry has no `- Why:` line:"]
            lines += [f"   `{a.key}`" for a in missing_reason]
        lines += ["", f"Add an entry to {LEDGER} in this change, with the reason, for example:", "",
                  "## <date> — <what changed>", "", "- Why: <why the check had to change, and why it "
                  "is not weaker; or who authorized it>", "- Changes:"]
        lines += [f"  - `{a.key}`" for a in pending]
    return "\n".join(lines) + "\n", 1 if pending else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", required=True, help="the commit the change is compared with")
    parser.add_argument("--head", required=True, help="the commit with the change")
    parser.add_argument("--repo", default=".", help="the repository (default: the current directory)")
    parser.add_argument("--summary", type=Path, help="also append the report to this Markdown file")
    args = parser.parse_args(argv)
    git = Git(args.repo)
    try:
        head = git.commit(args.head)
        base = git.merge_base(git.commit(args.base), head)
        anchors = changed_anchors(git, base, head)
        explained, unexplained = acknowledgements(git.text(base, LEDGER), git.text(head, LEDGER))
    except Fault as error:
        print(f"FAULT: {error}", file=sys.stderr)
        return 3
    text, code = report(anchors, explained, unexplained, base, head)
    print(text, end="")
    if args.summary:
        verdict = "needs acknowledgement" if code else "passed"
        with args.summary.open("a", encoding="utf-8") as summary:
            summary.write(f"### Trust-anchor guard: {verdict}\n\n```text\n{text}```\n")
    return code


if __name__ == "__main__":
    sys.exit(main())
