"""Score a classifier configuration for the constants track.  FROZEN.

  python constants/score_constants.py constants/candidate.json
  python constants/score_constants.py constants/candidate.json --accept results/constants_best.json

Objective (lower is better): product_unbiased = (sup_d d E[Y^2|d]) * (sup_d d E[W|d]),
an exact-recursion proxy for sup V*W / I_mu^2 of the unbiased estimator.
v4 proves the bound 12665; the universal lower bound is 1/16.

Validity: parameters within bounds, the Lemma 6 bias bound
e_N <= min{1, (N d^2)^-2} holding on dev and heldout grids, and a telescoping
residual below 1e-9. Acceptance requires a strict improvement on dev AND
heldout. These are finite-grid numbers, not proofs: any accepted configuration
must eventually get an analytic constant (Lean group G or a paper lemma).
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from evaluator import metrics  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
GRID = json.loads((ROOT / "constants" / "grid.json").read_text())


def evaluate(cfg: dict) -> dict:
    k1, k2 = float(cfg["k1"]), float(cfg["k2"])
    b = GRID["param_bounds"]
    in_bounds = b["k1"][0] <= k1 <= b["k1"][1] and b["k2"][0] <= k2 <= b["k2"][1]
    rng = np.random.default_rng(GRID["heldout_seed"])
    held = sorted(float(x) for x in 2.0 ** rng.uniform(-5, -1, GRID["heldout_count"]))
    t0 = time.time()
    dev = metrics(GRID["dev"], GRID["Lmax"], k1, k2)
    ho = metrics(held, GRID["Lmax"], k1, k2)
    valid = (in_bounds and dev["bias_ratio"] <= 1 and ho["bias_ratio"] <= 1
             and max(dev["tele_resid"], ho["tele_resid"]) < 1e-9)
    return {"config": {"k1": k1, "k2": k2}, "valid": valid, "in_bounds": in_bounds,
            "dev": dev, "heldout": ho,
            "score_dev": dev["product_unbiased"], "score_heldout": ho["product_unbiased"],
            "seconds": round(time.time() - t0, 1)}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("config", type=Path)
    ap.add_argument("--accept", type=Path)
    a = ap.parse_args()
    res = evaluate(json.loads(a.config.read_text()))
    (ROOT / "results").mkdir(exist_ok=True)
    (ROOT / "results" / "constants_last.json").write_text(json.dumps(res, indent=1))
    d, h = res["dev"], res["heldout"]
    print(f"valid={res['valid']} k1={res['config']['k1']} k2={res['config']['k2']} "
          f"product dev={res['score_dev']:.4f} heldout={res['score_heldout']:.4f} "
          f"(c1={d['c1_top']:.3f}, c2={d['c2_top']:.3f}; finite-budget product={d['product_finite']:.2f}; "
          f"bias_ratio={max(d['bias_ratio'], h['bias_ratio']):.3f}) [{res['seconds']}s]")
    if a.accept:
        prev = json.loads(a.accept.read_text()) if a.accept.exists() else None
        better = res["valid"] and (prev is None or (res["score_dev"] < prev["score_dev"]
                                                    and res["score_heldout"] < prev["score_heldout"]))
        print("ACCEPT" if better else "REJECT")
        if better:
            a.accept.write_text(json.dumps(res, indent=1))
        return 0 if better else 3
    return 0 if res["valid"] else 2


if __name__ == "__main__":
    sys.exit(main())
