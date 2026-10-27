"""Read-only validation of the frozen experiment; no new benchmark runs."""
from collections import defaultdict
from datetime import datetime, timezone
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
import csv
import hashlib
import json
import math
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    paths = ["feedback_experiment.py", "CONTRACT.md", "EXPERIMENT_LOCK.json",
             "EXPERIMENT_COMPLETE.json", "RAW.csv"]
    before = {name: sha(BASE / name) for name in paths}
    lock = json.loads((BASE / "EXPERIMENT_LOCK.json").read_text())
    complete = json.loads((BASE / "EXPERIMENT_COMPLETE.json").read_text())
    assert lock["source_sha256"] == before["feedback_experiment.py"]
    assert lock["contract_sha256"] == before["CONTRACT.md"]
    assert complete["lock_sha256"] == before["EXPERIMENT_LOCK.json"]
    assert complete["raw_sha256"] == before["RAW.csv"]
    spec = spec_from_file_location("audit_frozen_feedback", BASE / "feedback_experiment.py")
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    identities = module.identities()
    assert identities == lock["identity_checks"]
    truths = {}
    unseen_outside = {}
    for law in module.LAWS:
        for rho in module.RHOS:
            model = module.Model(law, rho)
            profiles = model.profiles()
            for name, q in profiles.items():
                truths[(law["name"], rho, name)] = float(model.mass @ q)
            unseen = profiles["unseen_mixture"]
            outside = not any(max(abs(unseen - row)) < 1e-14 for row in model.q)
            assert outside
            unseen_outside[f'{law["name"]}:{rho}'] = outside
    groups = defaultdict(list)
    total_work = 0
    with (BASE / "RAW.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    for row in rows:
        rho, theta, estimate, clipped = map(float,
            (row["rho"], row["theta"], row["estimate"], row["clipped"]))
        budget, work, coins, depth, rep = map(int,
            (row["budget"], row["work"], row["coins"], row["max_depth"], row["replicate"]))
        assert work == budget and work > 0
        assert 1 <= coins <= budget and 1 <= depth <= budget
        assert work <= coins * depth
        assert math.isfinite(estimate) and -1e-14 <= estimate <= rho + 1e-14
        assert clipped == min(1, max(0, estimate))
        assert abs(theta - truths[(row["law"], rho, row["profile"])]) < 1e-14
        assert float(row["seconds"]) >= 0
        if row["mode"] == "fresh":
            assert depth == 1 and coins == budget
        elif row["mode"].startswith("block"):
            block = int(row["mode"][5:])
            assert depth == block and coins == budget // block
        else:
            assert row["mode"] == "feedback"
        groups[(row["law"], rho, row["profile"], budget, row["mode"])].append(rep)
        total_work += work
    assert len(rows) == complete["rows"] == 7680
    assert len(groups) == 240
    assert all(sorted(reps) == list(range(32)) for reps in groups.values())
    assert total_work == 3440640
    after = {name: sha(BASE / name) for name in paths}
    assert before == after
    result = dict(status="PASS: frozen source/contract/raw hashes and finite accounting",
        utc=datetime.now(timezone.utc).isoformat(), source_sha256_before=before,
        audit_checker_sha256=sha(Path(__file__)),
        source_sha256_after=after, identity_checks=identities, rows=len(rows),
        cells=len(groups), replicates_per_cell=32, charged_flips=total_work,
        unseen_profiles_outside_prior=unseen_outside,
        limitations=["No new benchmark run or Monte Carlo precision improvement",
            "Numerical predictive checks compare float64 with exact binary-rational inputs",
            "Per-row times exclude Model setup and share a warmed predictive cache",
            "Known finite prior is a design choice, not an oracle for unknown true q",
            "No confidence interval estimator or coverage guarantee"])
    target = HERE / (sys.argv[1] if len(sys.argv) == 2 else "experiment_audit.json")
    if target.parent.resolve() != HERE.resolve() or target.exists():
        raise RuntimeError("Output must be a new file in this audit directory")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS: 7680 rows; 240 cells; 3440640 charged flips; source/contract/raw lock identities")


if __name__ == "__main__":
    main()
