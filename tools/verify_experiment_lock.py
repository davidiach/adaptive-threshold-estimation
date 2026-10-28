"""Check selection provenance and recompute summaries from stored test data.

This does not draw new held-out samples or rerun tuning.
"""
from hashlib import sha256
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    # Explicit checks, unlike assert, still run under python -O.
    if not condition:
        raise RuntimeError(message)


def digest(relative):
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def main():
    lock = json.loads((ROOT / "results/real_selection.json").read_text())
    for name, expected in lock["hashes"].items():
        if digest(name) != expected:
            raise SystemExit(f"Locked benchmark input changed: {name}")
    started = json.loads((ROOT / "results/real_test_started.json").read_text())
    require(started["selection_sha256"] == digest("results/real_selection.json"),
            "test start record does not match the locked selection")
    for copy, original in [("reference.py", "code/benchmark.py"),
                           ("data/training.json", "results/training.json"),
                           ("data/tuning.json", "results/tuning.json")]:
        require(digest("benchmark/" + copy) == digest("inputs/next-phase/" + original),
                "benchmark copy differs from its original input")
    test = json.loads((ROOT / "results/real_test.json").read_text())
    raw = np.load(ROOT / "results/real_test_raw.npz")
    for row in test["rows"]:
        key = f"{row['method']}_{row['budget']}"
        values, work = raw[key + "_value"], raw[key + "_work"]
        require(len(values) == row["n"] == lock["heldout_replications"],
                "held-out replication count changed")
        rmse = np.sqrt(np.mean((np.clip(values, 0, 1) - .025)**2))
        require(np.isclose(rmse, row["rmse"], rtol=1e-12, atol=1e-14),
                "recorded RMSE does not match the raw held-out data")
        require(np.isclose(work.mean(), row["mean_work"], rtol=1e-12, atol=1e-12),
                "recorded mean work does not match the raw held-out data")
    constants = json.loads((ROOT / "results/constants_candidate_lock.json").read_text())
    for key, name in [("search_sha256", "results/constants_dev_search.jsonl"),
                      ("scorer_sha256", "constants/score_constants.py"),
                      ("evaluator_sha256", "constants/evaluator.py")]:
        require(constants[key] == digest(name), "locked constants source changed")
    for field, filename in [("candidate", "constants/candidate_finite_grid.json"),
                            ("theory_compatible_candidate", "constants/candidate_theory.json")]:
        require(constants[field]["config"] == json.loads((ROOT / filename).read_text()),
                "accepted constants configuration changed")
    print(f"Verified {len(lock['hashes'])} benchmark locks, constants selections, and {len(test['rows'])} raw-data summaries.")


if __name__ == "__main__":
    main()
