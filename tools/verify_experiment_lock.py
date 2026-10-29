"""Check selection provenance and recompute the held-out record from its raw data.

The held-out record must hold exactly the locked selection's cells, with their
seeds and configurations, and every summary and the accept decision must follow
from the raw arrays. This does not draw new held-out samples or rerun tuning.
CI passes --strict, which requires every committed locked file to match its
lock byte for byte.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "benchmark"))
import reference as ref  # noqa: E402  (the locked copy of the original benchmark code)

# The held-out run (results/real_test.json and its raw arrays) was sealed when
# it finished; these digests were recorded afterwards, on 29 October 2026.
HELDOUT = {
    "results/real_test.json": "1f53cdd95e60d21db21b9142ece6694769a599021bf27b7a64605bd55e3856a5",
    "results/real_test_raw.npz": "129ea8ad8b65f77950350c05234e2ba2a5c6ea98b8b1c91fa0fb68c1ef2116b5",
}
# run_real.py's method index in the test seed formula 41000+100*budget_index+method_index.
METHODS = (("gha_tuned", 1), ("real_tuned", 4))
# benchmark/verify_real.py rewrites this locked record with the platform's line
# endings, and the locked copy was written with CRLF. Running it on Linux must
# not break a local lock check, so outside --strict this one file may differ
# from its lock in line endings only.
REWRITTEN = {"results/real_verification.json"}


def require(condition, message):
    # Explicit checks, unlike assert, still run under python -O.
    if not condition:
        raise RuntimeError(message)


def digest(relative):
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def matches_lock(name, data, expected, strict=False):
    """True if data hashes to its lock. Unless strict, REWRITTEN files may differ
    only in using LF or CRLF line endings throughout."""
    if sha256(data).hexdigest() == expected:
        return True
    if strict or name not in REWRITTEN:
        return False
    lf = data.replace(b"\r\n", b"\n")
    crlf = lf.replace(b"\n", b"\r\n")
    return (b"\r" not in lf and data in (lf, crlf)
            and any(sha256(form).hexdigest() == expected for form in (lf, crlf)))


def close(actual, expected, what):
    actual, expected = np.asarray(actual, dtype=float), np.asarray(expected, dtype=float)
    require(actual.shape == expected.shape and np.allclose(actual, expected, rtol=1e-12, atol=1e-14),
            f"{what} does not match the raw held-out data")


def check_sealed():
    """The test-start record pins the locked selection, and the sealed results are unchanged."""
    started = json.loads((ROOT / "results/real_test_started.json").read_text())
    require(started["selection_sha256"] == digest("results/real_selection.json"),
            "test start record does not match the locked selection")
    for name, expected in HELDOUT.items():
        require(digest(name) == expected, f"sealed held-out result changed: {name}")


def check_heldout(lock, test, raw, training):
    """Require the held-out record to be exactly the locked cells, recomputed from raw data.

    `lock` is the selection, `test` the held-out record, `raw` its arrays by key
    and `training` the GHA training record. Returns the recomputed accept decision.
    """
    n = lock["heldout_replications"]
    cells = [(method, spec["budget"], 41000 + 100*ref.BUDGETS.index(spec["budget"]) + index, index, spec)
             for spec in lock["rows"] for method, index in METHODS]
    require(isinstance(test.get("rows"), list)
            and [(row.get("method"), row.get("budget")) for row in test["rows"]]
            == [(method, budget) for method, budget, *_ in cells],
            "held-out rows are not exactly the locked selection's cells")
    require(set(raw) == {f"{method}_{budget}_{kind}" for method, budget, *_ in cells for kind in ("value", "work")},
            "raw held-out arrays are not exactly the locked selection's cells")
    rmse = {}
    for row, (method, budget, seed, index, spec) in zip(test["rows"], cells):
        what = f"held-out {method} at {budget}"
        values, work = raw[f"{method}_{budget}_value"], raw[f"{method}_{budget}_work"]
        require(values.shape == work.shape == (n,) and np.isfinite(values).all()
                and np.isfinite(work).all() and (work > 0).all(),
                f"{what}: raw arrays are not {n} finite values and positive work counts")
        require(row["seed"] == seed, f"{what}: seed is not the locked test seed formula")
        if method == "gha_tuned":
            require(row["config"] == spec["gha"]["config"], f"{what}: configuration is not the locked one")
            levels, counts, planned = ref.allocate(budget, training, f"gha_{spec['gha']['index']}")
            require(row["levels"] == levels.tolist() and row["counts"] == counts.tolist(),
                    f"{what}: allocation is not the locked training allocation")
            close(row["planned_work"], planned, f"{what}: planned work")
        else:
            chosen = spec["candidate"]
            require(row["config"] == chosen["config"] and row["law"] == chosen["law"]
                    and row["probabilities"] == chosen["probabilities"],
                    f"{what}: configuration or level law is not the locked one")
        for field, value in ref.summarize(values, work).items():
            close(row[field], value, f"{what}: {field}")
        # run_real.py's descriptive bootstrap, seeded 51000+100*budget_index+method_index.
        sample = np.random.default_rng(seed + 10000).integers(0, n, size=(3000, n))
        errors = (np.clip(values, 0, 1) - ref.THETA)**2
        close(row["rmse_interval"], np.quantile(np.sqrt(errors[sample].mean(axis=1)), [.025, .975]),
              f"{what}: RMSE interval")
        close(row["work_interval"], np.quantile(work[sample].mean(axis=1), [.025, .975]),
              f"{what}: work interval")
        rmse[method, budget] = row["rmse"]
    accept = all(rmse["real_tuned", spec["budget"]] < rmse["gha_tuned", spec["budget"]] for spec in lock["rows"])
    require(test.get("complete") is True and test.get("replications") == n,
            "held-out record is incomplete")
    require(test.get("baseline_zero_rmse") == lock["baseline_zero_rmse"] == ref.THETA,
            "held-out zero baseline is not the locked one")
    close(test["total_work"], sum(row["mean_work"]*n for row in test["rows"]), "held-out total work")
    require(test.get("accept") is accept, f"held-out accept should be {accept}, as the raw data give")
    return accept


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", action="store_true",
                        help="require exact locked bytes; CI runs this before verify_real.py")
    strict = parser.parse_args(argv).strict
    lock = json.loads((ROOT / "results/real_selection.json").read_text())
    for name, expected in lock["hashes"].items():
        if not matches_lock(name, (ROOT / name).read_bytes(), expected, strict):
            raise SystemExit(f"Locked benchmark input changed: {name}")
    for copy, original in [("reference.py", "code/benchmark.py"),
                           ("data/training.json", "results/training.json"),
                           ("data/tuning.json", "results/tuning.json")]:
        require(digest("benchmark/" + copy) == digest("inputs/next-phase/" + original),
                "benchmark copy differs from its original input")
    check_sealed()
    test = json.loads((ROOT / "results/real_test.json").read_text())
    training = json.loads((ROOT / "benchmark/data/training.json").read_text())["training"]
    with np.load(ROOT / "results/real_test_raw.npz") as raw:
        accept = check_heldout(lock, test, dict(raw), training)
    constants = json.loads((ROOT / "results/constants_candidate_lock.json").read_text())
    for key, name in [("search_sha256", "results/constants_dev_search.jsonl"),
                      ("scorer_sha256", "constants/score_constants.py"),
                      ("evaluator_sha256", "constants/evaluator.py")]:
        require(constants[key] == digest(name), "locked constants source changed")
    for field, filename in [("candidate", "constants/candidate_finite_grid.json"),
                            ("theory_compatible_candidate", "constants/candidate_theory.json")]:
        require(constants[field]["config"] == json.loads((ROOT / filename).read_text()),
                "accepted constants configuration changed")
    print(f"Verified {len(lock['hashes'])} benchmark locks, constants selections, and the "
          f"{len(test['rows'])} locked held-out cells from raw data (accept={accept}).")


if __name__ == "__main__":
    main()
