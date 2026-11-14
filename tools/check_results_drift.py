"""Fail when a legacy check's regenerated record differs from the committed one.

Several older checks rewrite tracked records under results/ instead of
temporary output: benchmark/verify_real.py, tools/check_power_bracket.py,
proposals/constants/bias_audit.py, proposals/constants/uniform_constant_checks.py
and constants/score_constants.py. CI runs them without comparing their output
with the committed records, so a changed replay would pass unnoticed.

Run this after those checks. It parses each rewritten JSON record and compares
it with the committed version of the same path. Line endings are ignored (the
committed records use CRLF; a Linux run writes LF), and so are wall-clock
fields. Floats must agree within a relative tolerance of 1e-9 or an absolute
tolerance of 1e-12: this admits last-digit floating-point noise but not a
changed result. The check only reads files; use a disposable checkout or CI,
since the checks before it rewrite published records.

With --rewritten-since MARKER each record must also be newer than the marker
file, which CI creates before the checks run: a check that stopped writing its
record would otherwise leave the committed bytes in place and pass. constants/
score_constants.py writes the same file for every configuration, so CI keeps a
copy after each run; --extra COPY=RECORD compares such a copy with the
committed record it reproduces.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import subprocess
import sys
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]

# Each record rewritten in place by a CI step, with its wall-clock fields.
RECORDS: dict[str, frozenset[str]] = {
    "results/real_verification.json": frozenset(),
    "results/power_bracket.json": frozenset(),
    "results/constants_bias_counterexample.json": frozenset(),
    "results/constants_uniform_bound.json": frozenset(),
    "results/constants_last.json": frozenset({"seconds"}),
}
REL_TOL = 1e-9
ABS_TOL = 1e-12


def _number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def compare(committed: object, current: object, volatile: frozenset[str] = frozenset(),
            where: str = "$") -> list[str]:
    """List the differences between two parsed JSON values."""
    if isinstance(committed, dict) and isinstance(current, dict):
        differences = []
        for key in sorted(set(committed) | set(current)):
            if key in volatile:
                continue
            if key not in current:
                differences.append(f"{where}.{key}: missing from the regenerated record")
            elif key not in committed:
                differences.append(f"{where}.{key}: not in the committed record")
            else:
                differences += compare(committed[key], current[key], volatile, f"{where}.{key}")
        return differences
    if isinstance(committed, list) and isinstance(current, list):
        if len(committed) != len(current):
            return [f"{where}: length {len(committed)} became {len(current)}"]
        differences = []
        for index, (old, new) in enumerate(zip(committed, current)):
            differences += compare(old, new, volatile, f"{where}[{index}]")
        return differences
    if _number(committed) and _number(current):
        if isinstance(committed, int) and isinstance(current, int):
            same = committed == current
        elif math.isnan(committed) or math.isnan(current):
            same = math.isnan(committed) and math.isnan(current)
        else:
            same = math.isclose(committed, current, rel_tol=REL_TOL, abs_tol=ABS_TOL)
        return [] if same else [f"{where}: {committed!r} became {current!r}"]
    if type(committed) is not type(current) or committed != current:
        return [f"{where}: {committed!r} became {current!r}"]
    return []


def git_bytes(path: str, ref: str) -> bytes:
    return subprocess.run(["git", "show", f"{ref}:{path}"], cwd=ROOT, check=True,
                          capture_output=True).stdout


def check(records: dict[str, frozenset[str]], committed: Callable[[str], bytes],
          current: Callable[[str], bytes]) -> list[str]:
    problems = []
    for path, volatile in records.items():
        try:
            old, new = committed(path), current(path)
        except (OSError, subprocess.CalledProcessError) as error:
            problems.append(f"{path}: cannot read ({error})")
            continue
        if old == new:
            continue
        try:
            differences = compare(json.loads(old), json.loads(new), volatile)
        except ValueError as error:
            problems.append(f"{path}: not valid JSON ({error})")
            continue
        problems += [f"{path} {difference}" for difference in differences]
    return problems


def stale(paths: list[str], marker: Path) -> list[str]:
    """Records not rewritten since the marker was created."""
    since = marker.stat().st_mtime
    return [f"{path}: not rewritten by its check" for path in paths
            if not (ROOT / path).is_file() or (ROOT / path).stat().st_mtime < since]


def extra_pairs(values: list[str]) -> dict[str, str]:
    pairs = {}
    for value in values:
        copy, sep, record = value.partition("=")
        if not sep or not copy or not record.startswith("results/"):
            raise ValueError("--extra expects COPY=results/RECORD, got " + value)
        pairs[copy] = record
    return pairs


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--ref", default="HEAD", help="commit holding the published records")
    parser.add_argument("--rewritten-since", type=Path,
                        help="marker file created before the checks; every record must be newer")
    parser.add_argument("--extra", action="append", default=[],
                        help="COPY=results/RECORD: compare a kept copy with a committed record")
    args = parser.parse_args(argv)
    problems = check(RECORDS, lambda path: git_bytes(path, args.ref),
                     lambda path: (ROOT / path).read_bytes())
    pairs = extra_pairs(args.extra)
    volatile = frozenset({"seconds"})
    problems += check({copy: volatile for copy in pairs},
                      lambda copy: git_bytes(pairs[copy], args.ref),
                      lambda copy: (ROOT / copy).read_bytes())
    if args.rewritten_since:
        problems += stale(list(RECORDS) + list(pairs), args.rewritten_since)
    if problems:
        print("Regenerated records differ from the committed ones:")
        print("\n".join("  " + problem for problem in problems))
        print("Commit the regenerated record only if the change is intended and explained.")
        return 1
    print(f"{len(RECORDS) + len(pairs)} regenerated records match the committed ones at {args.ref}"
          + (", all rewritten by their checks." if args.rewritten_since else "."))
    return 0


if __name__ == "__main__":
    sys.exit(main())
