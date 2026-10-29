"""Scan every project Lean source for proof escapes.

The frozen Tier 3-6 verifiers scan every module in their directories, including
unfrozen proof modules, with the frozen Tier 6 pattern. That pattern misses the
`admit` tactic and `#guard_msgs`, and its comment stripper parses neither string
literals nor escaped identifiers, so "/-" or «/-» could hide `run_cmd` or
`set_option debug.skipKernelTC true` after it. This unfrozen check applies the
strengthened shared pattern to every project Lean source, so those gaps are
closed without changing frozen files. It needs no Lean build.
"""
from __future__ import annotations

from pathlib import Path
import sys

from verify_blind_upper_components import FORBIDDEN, strip_comments

ROOT = Path(__file__).resolve().parents[1]
GENERATED = {".lake", ".audit"}  # build output and verifier-written audit files


def sources(root: Path = ROOT) -> list[Path]:
    """Project Lean sources; research/ and inputs/ keep their own hash locks."""
    lean = [p for p in (root / "lean").rglob("*.lean")
            if not GENERATED & set(p.relative_to(root / "lean").parts)]
    return sorted(lean + list((root / "proposals/constants").glob("*.lean")))


def violations(paths: list[Path]) -> list[str]:
    found = []
    for path in paths:
        try:
            match = FORBIDDEN.search(strip_comments(path.read_text(encoding="utf-8")))
        except ValueError as error:  # an unclosed block comment
            found.append(f"{path}: {error}")
            continue
        if match:
            line = match.string.count("\n", 0, match.start())+1
            found.append(f"{path}:{line}: forbidden {match.group()!r}")
    return found


def main() -> int:
    paths = sources()
    found = violations(paths)
    if found or not paths:
        print("\n".join(found) or "No Lean sources found")
        return 1
    print(f"Checked {len(paths)} Lean sources: no proof escapes.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
