"""Check selection provenance and recompute summaries from stored test data.

This does not draw new held-out samples or rerun tuning.
"""
from hashlib import sha256
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def digest(relative):
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def main():
    lock = json.loads((ROOT / "results/real_selection.json").read_text())
    for name, expected in lock["hashes"].items():
        if digest(name) != expected:
            raise SystemExit(f"Locked benchmark input changed: {name}")
    started = json.loads((ROOT / "results/real_test_started.json").read_text())
    assert started["selection_sha256"] == digest("results/real_selection.json")
    for copy, original in [("reference.py", "code/benchmark.py"),
                           ("data/training.json", "results/training.json"),
                           ("data/tuning.json", "results/tuning.json")]:
        assert digest("benchmark/" + copy) == digest("inputs/next-phase/" + original)
    test = json.loads((ROOT / "results/real_test.json").read_text())
    raw = np.load(ROOT / "results/real_test_raw.npz")
    for row in test["rows"]:
        key = f"{row['method']}_{row['budget']}"
        values, work = raw[key + "_value"], raw[key + "_work"]
        assert len(values) == row["n"] == lock["heldout_replications"]
        rmse = np.sqrt(np.mean((np.clip(values, 0, 1) - .025)**2))
        assert np.isclose(rmse, row["rmse"], rtol=1e-12, atol=1e-14)
        assert np.isclose(work.mean(), row["mean_work"], rtol=1e-12, atol=1e-12)
    constants = json.loads((ROOT / "results/constants_candidate_lock.json").read_text())
    for key, name in [("search_sha256", "results/constants_dev_search.jsonl"),
                      ("scorer_sha256", "constants/score_constants.py"),
                      ("evaluator_sha256", "constants/evaluator.py")]:
        assert constants[key] == digest(name)
    for field, filename in [("candidate", "constants/candidate_finite_grid.json"),
                            ("theory_compatible_candidate", "constants/candidate_theory.json")]:
        assert constants[field]["config"] == json.loads((ROOT / filename).read_text())
    print(f"Verified {len(lock['hashes'])} benchmark locks, constants selections, and {len(test['rows'])} raw-data summaries.")


if __name__ == "__main__":
    main()
