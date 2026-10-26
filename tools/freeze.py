"""Phase 0 freeze: record SHA-256 of every file agents must not change.

  python tools/freeze.py --init     # only once, after the Phase 0 compile gate
  python tools/freeze.py --verify   # same check the scorer runs

Re-freezing after Phase 0 requires human approval: delete FROZEN.sha256 only
when David has approved the change recorded in FREEZE_LOG.md.
"""
from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FROZEN = [
    "lean/ThresholdHC/Statements.lean",
    "lean/ThresholdHC/Statements2.lean",
    "lean/ThresholdHC.lean",
    "lean/lakefile.toml",
    "lean/lean-toolchain",
    "lean/lake-manifest.json",
    "tools/targets.json",
    "tools/score.py",
    "tools/freeze.py",
    "tools/check_targets_numeric.py",
    "tools/check_targets2_numeric.py",
    "lean/ThresholdHC/Uniform713/Specification.lean",
    "lean/ThresholdHC/Uniform713/Common.lean",
    "lean/ThresholdHC/Uniform713/Concentration.lean",
    "lean/ThresholdHC/Uniform713/Classifier.lean",
    "lean/ThresholdHC/Uniform713/Estimator.lean",
    "tools/uniform713_targets.json",
    "tools/verify_uniform713.py",
    "constants/evaluator.py",
    "constants/score_constants.py",
    "constants/grid.json",
]


def digest(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--init", action="store_true")
    g.add_argument("--verify", action="store_true")
    a = ap.parse_args()
    manifest = ROOT / "FROZEN.sha256"
    if a.init:
        if manifest.exists():
            print("Already frozen. Changing frozen files needs David's approval (see BRIEF.md).")
            return 1
        missing = [f for f in FROZEN if not (ROOT / f).exists()]
        if missing:
            print("Cannot freeze; missing files (finish Phase 0 setup first):", missing)
            return 1
        lines = ["# sha256  path   (written by tools/freeze.py --init)"]
        lines += [f"{digest(ROOT / f)}  {f}" for f in FROZEN]
        manifest.write_text("\n".join(lines) + "\n")
        print(f"Froze {len(FROZEN)} files.")
        return 0
    bad = []
    for line in manifest.read_text().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        h, f = line.split(maxsplit=1)
        if not (ROOT / f).exists() or digest(ROOT / f) != h:
            bad.append(f)
    print("OK" if not bad else f"MODIFIED: {bad}")
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
