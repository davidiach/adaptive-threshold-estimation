"""Rebuild and enforce complete, successful audits without changing the scorer.

The frozen scorer is retained byte-for-byte. This additional guard checks its
audit subprocess exit status and complete reports, then prevents regression
against the committed best result. Use --sequential on memory-limited runners.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

import score

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sequential", action="store_true")
    parser.add_argument("--accept", type=Path,
                        help="Require the frozen scorer to accept an improvement over this JSON")
    args = parser.parse_args()
    if args.sequential:
        for group in ("Algebra", "FixedGap", "Calibration", "Modulus", "Constants",
                      "Classifier", "Hellinger", "KL"):
            subprocess.run(["lake", "build", f"ThresholdHC.Proofs.{group}"],
                           cwd=LEAN, check=True)
    command = [sys.executable, str(ROOT / "tools/score.py")]
    if args.accept:
        command += ["--accept", str(args.accept.resolve())]
    subprocess.run(command, cwd=ROOT, check=True)
    audit_file, spans = score.write_audit()
    result = subprocess.run(["lake", "env", "lean", str(audit_file.relative_to(LEAN))],
                            cwd=LEAN, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (ROOT / "results/lean_independent_audit.log").write_text(output, encoding="utf-8")
    statuses = score.parse_audit(output, spans)
    complete = (len(statuses) == len(spans) and
                all(s["status"] in {"proven", "sorry"} for s in statuses.values()))
    current = json.loads((ROOT / "results/lean_score.json").read_text())
    best_path = ROOT / "results/lean_best.json"
    best = json.loads(best_path.read_text()) if best_path.exists() else {"proven": [], "points": 0}
    proven = {name for name, s in statuses.items() if s["status"] == "proven"}
    consistent = (proven == set(current["proven"]) and statuses == current["targets"])
    no_regression = set(best["proven"]).issubset(proven) and current["points"] >= best["points"]
    ok = result.returncode == 0 and complete and consistent and no_regression and current["valid"]
    checkpoint = dict(valid=ok, audit_exit_code=result.returncode, complete=complete,
                      target_count=len(statuses), consistent_with_scorer=consistent,
                      no_regression=no_regression, points=current["points"],
                      proven=sorted(proven))
    (ROOT / "results/lean_checkpoint.json").write_text(json.dumps(checkpoint, indent=2) + "\n")
    print(json.dumps(checkpoint, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
