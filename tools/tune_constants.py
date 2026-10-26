"""Deterministic development-only search; never reads or constructs held-out data.

Run from the kit root: python tools/tune_constants.py --stage coarse
Then run --stage refine. Both stages write every tested point to JSONL.
The final --select command locks a candidate without invoking the acceptance
scorer. Run constants/score_constants.py separately, once, after selection.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "constants"))
from evaluator import metrics, profile

GRID = json.loads((ROOT / "constants/grid.json").read_text())
LOG = ROOT / "results/constants_dev_search.jsonl"


def evaluate(params):
    k1, k2 = params
    t0 = time.perf_counter()
    result = metrics(GRID["dev"], GRID["Lmax"], k1, k2)
    profile.cache_clear()
    return {"config": {"k1": k1, "k2": k2}, "dev": result,
            "dev_valid": result["bias_ratio"] <= 1 and result["tele_resid"] < 1e-9,
            "seconds": time.perf_counter() - t0}


def read_rows():
    return [json.loads(line) for line in LOG.read_text().splitlines()] if LOG.exists() else []


def best_row(rows):
    return min((r for r in rows if r["dev_valid"]), key=lambda r: r["dev"]["product_unbiased"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", choices=["coarse", "refine", "fine"])
    parser.add_argument("--select", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    rows = read_rows()
    if args.select:
        chosen = best_row(rows)
        conservative = best_row([r for r in rows if r["config"]["k2"] >= 1])
        lock = {"status": "selected before held-out acceptance", "selection": "minimum valid dev objective",
                "trials": len(rows), "candidate": chosen,
                "theory_compatible_candidate": conservative,
                "acceptance_order": ["theory_compatible", "finite_grid_winner"],
                "warning": "The finite-grid winner has a proved off-grid bias-bound counterexample; see proposals/constants/BIAS_AUDIT.md",
                "search_sha256": hashlib.sha256(LOG.read_bytes()).hexdigest(),
                "scorer_sha256": hashlib.sha256((ROOT / "constants/score_constants.py").read_bytes()).hexdigest(),
                "evaluator_sha256": hashlib.sha256((ROOT / "constants/evaluator.py").read_bytes()).hexdigest(),
                "seed": None, "randomness": "none: exact-recursion floating-point development grid"}
        lock_path = ROOT / "results/constants_candidate_lock.json"
        if lock_path.exists():
            raise SystemExit("Candidate already locked; refusing overwrite")
        lock_path.write_text(json.dumps(lock, indent=2) + "\n")
        (ROOT / "constants/candidate_theory.json").write_text(json.dumps(conservative["config"], indent=2) + "\n")
        (ROOT / "constants/candidate_finite_grid.json").write_text(json.dumps(chosen["config"], indent=2) + "\n")
        (ROOT / "constants/candidate.json").write_text(json.dumps(conservative["config"], indent=2) + "\n")
        print(json.dumps(lock, indent=2))
        return
    if (ROOT / "results/constants_candidate_lock.json").exists():
        raise SystemExit("Candidate locked; no post-acceptance tuning in this run")
    if args.stage == "coarse":
        points = itertools.product([.25, .35, .5, .65, .8, 1., 1.25, 1.5, 2., 3., 4.],
                                   [.5, .6, .7, .85, 1., 1.25, 1.5, 2., 3., 4.])
    elif args.stage in ("refine", "fine"):
        best = best_row(rows)["config"]
        step = .05 if args.stage == "refine" else .01
        radius = 5
        points = itertools.product([round(best["k1"] + step * i, 8) for i in range(-radius, radius + 1)],
                                   [round(best["k2"] + step * i, 8) for i in range(-radius, radius + 1)])
    else:
        parser.error("Specify --stage or --select")
    known = {(r["config"]["k1"], r["config"]["k2"]) for r in rows}
    points = sorted(set((a, b) for a, b in points if .25 <= a <= 4 and .5 <= b <= 4) - known)
    print(f"stage={args.stage}, new trials={len(points)}, workers={args.workers}", flush=True)
    with ProcessPoolExecutor(max_workers=args.workers) as pool, LOG.open("a", encoding="utf-8") as log:
        for i, row in enumerate(pool.map(evaluate, points), 1):
            row["stage"] = args.stage
            log.write(json.dumps(row) + "\n")
            log.flush()
            rows.append(row)
            if i % 10 == 0 or i == len(points):
                best = best_row(rows)
                print(f"{i}/{len(points)} best={best['config']} dev={best['dev']['product_unbiased']:.8f} "
                      f"bias={best['dev']['bias_ratio']:.8f}", flush=True)


if __name__ == "__main__":
    main()
