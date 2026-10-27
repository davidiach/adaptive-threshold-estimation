"""Read-only old-source checks and isolated diagnostics for the critical note.

No old verifier output, experiment record, or Lean evidence is overwritten.
The scalar checks are exact arithmetic diagnostics, not a formal theorem proof.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def scalar_checks():
    checks = {
        "prefix_KL": F(64, 3) / 1024 == F(1, 48),
        "pinsker_squared": F(1, 96) < F(1, 64),
        "window_mass": 1 - F(2, 10) - F(1, 8) - F(1, 4) > F(1, 4),
        "unbiased_repeat_envelope": 256 + 256 + 1 == 513,
        "unbiased_chebyshev_sup": F(128, 9 * 256) < F(1, 10),
        "unbiased_product_coefficient": F(16, 3) * 513 * F(4, 3) == 3648,
        "low_bias_variance": F(3, 4) * F(31, 32) ** 2 >= F(2, 3),
        "low_bias_second_to_variance": 1 + F(3, 8) * F(65, 64) ** 2 <= F(3, 2),
        "low_bias_repeat_envelope": F(513) / F(2, 3) + 512 <= 1282,
        "low_bias_chebyshev_sup": F(32, 512) < F(1, 10),
        "low_bias_product_coefficient": F(16, 3) * 1282 * 4 <= 30000,
        "additive_variance_factor": 1 + 4 * F(1, 4) / (1 - F(1, 4)) == F(7, 3),
        "upper_second_moment_sum": F(35, 16) + F(85, 16) / 7 == F(165, 56),
        "upper_work_sum": 2 * F(225, 2) * 6 == 1350,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


def main():
    baseline = json.loads((HERE / "BASELINE.json").read_text(encoding="utf-8"))
    protected = []
    concurrent_changes = []
    for rel, digest in baseline["sha256"].items():
        current = sha(ROOT / rel) if (ROOT / rel).is_file() else None
        # Tier5 proof/evidence belongs to concurrent work, not this checkpoint.
        concurrent = "Tier5" in rel or "tier5" in rel
        core = rel.startswith(("lean/", "tools/", "inputs/", "constants/", "benchmark/", "results/",
                               "research/2026-10-27-route-a/")) or rel == "paper/paper.tex"
        if (core and not concurrent) or rel.endswith("FROZEN.sha256"):
            if current != digest:
                raise RuntimeError("Protected baseline changed: " + rel)
            protected.append(rel)
        elif current != digest:
            concurrent_changes.append({"path": rel, "baseline": digest, "current": current})

    lock_entries = 0
    for name in ("FROZEN.sha256", "TIER3_FROZEN.sha256", "TIER4_FROZEN.sha256", "TIER5_FROZEN.sha256"):
        for line in (ROOT / name).read_text(encoding="utf-8").splitlines():
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            digest, rel = line.split(maxsplit=1)
            if sha(ROOT / rel.strip()) != digest:
                raise RuntimeError("Lock mismatch: " + rel)
            lock_entries += 1
    bridge_lock = json.loads((ROOT / "lean/ThresholdHC/ResearchRouteA/SPEC_LOCK_v1.json").read_text())
    for rel, digest in bridge_lock["locked_sha256"].items():
        if sha(ROOT / rel) != digest:
            raise RuntimeError("Bridge lock mismatch: " + rel)
        lock_entries += 1

    paper_lock = json.loads((HERE / "CHECKPOINT_LOCK_v1.json").read_text(encoding="utf-8"))
    for rel, digest in paper_lock["sha256"].items():
        if sha(ROOT / rel) != digest:
            raise RuntimeError("Paper checkpoint mismatch: " + rel)
    paper_hash = sha(HERE / "construction.tex")
    for name in ("review.md", "second-review.md"):
        if paper_hash not in (HERE / name).read_text(encoding="utf-8"):
            raise RuntimeError("Exact final-source review identity missing: " + name)
    compilation = json.loads((HERE / "compilation.json").read_text(encoding="utf-8"))
    if compilation["kind"] != "success" or compilation["source_sha256"] != paper_hash:
        raise RuntimeError("Compilation record does not match final source")

    scalar = scalar_checks()
    records = []
    env = dict(os.environ, PYTHONUTF8="1")
    # Only read-only or temporary-directory old checks. Published results stay intact.
    commands = [
        ("freeze", ["tools/freeze.py", "--verify"]),
        ("inputs", ["tools/verify_inputs.py"]),
        ("regressions", ["-m", "unittest", "discover", "-s", "tools", "-p", "test_*.py", "-v"]),
    ]
    for name, args in commands:
        start = time.monotonic()
        proc = subprocess.run([sys.executable, *args], cwd=ROOT, env=env,
                              capture_output=True, text=True, encoding="utf-8")
        (HERE / ("validation-" + name + ".log")).write_text(proc.stdout + proc.stderr, encoding="utf-8")
        records.append({"command": [sys.executable, *args], "exit_code": proc.returncode,
                        "seconds": time.monotonic() - start})
        if proc.returncode:
            raise RuntimeError(proc.stdout + proc.stderr)

    import fisher
    sanity = fisher.sanity_checks() if hasattr(fisher, "sanity_checks") else None
    if sanity is None:
        raise RuntimeError("Fisher sanity checks unavailable; inspect the diagnostic interface")
    # Recompute every recorded policy; keep the original numerical record intact.
    prior = json.loads((HERE / "fisher.json").read_text(encoding="utf-8"))
    replay = []
    for old in prior["cases"]:
        new = fisher.run_case(old["K"], old["horizon"])
        if new["policy_sha256"] != old["policy_sha256"]:
            raise RuntimeError("Numerical policy replay differs")
        for key in ("expected_work", "fisher_information", "fisher_per_expected_work"):
            if abs(new[key] - old[key]) > 1e-12 * max(1.0, abs(old[key])):
                raise RuntimeError("Numerical replay differs: " + key)
        replay.append({"K": old["K"], "horizon": old["horizon"],
                       "policy_sha256": new["policy_sha256"]})

    sources = sorted(p for p in HERE.iterdir() if p.suffix in (".tex", ".md", ".py"))
    sources += [ROOT / p for p in ("docs/process/REPORT.md", "docs/process/RUNLOG.md",
                                  "docs/RESULTS.md", "docs/VERIFY.md", "paper/UPDATES.md")]
    result = {
        "valid": True,
        "scope": "Paper-proof artifact, old-source preservation, exact scalar checks, finite numerical replay; no new Lean theorem",
        "head_at_replay": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip(),
        "protected_baseline_files_unchanged": len(protected),
        "lock_entries_verified": lock_entries,
        "paper_checkpoint_lock_sha256": sha(HERE / "CHECKPOINT_LOCK_v1.json"),
        "final_paper_source_sha256": paper_hash,
        "compilation_source_matches": True,
        "nonprotected_baseline_changes": concurrent_changes,
        "exact_scalar_checks": scalar,
        "commands": records,
        "fisher_sanity": sanity,
        "fisher_replayed_cases": replay,
        "source_sha256": {str(p.relative_to(ROOT)).replace("\\", "/"): sha(p) for p in sources},
        "new_Lean_targets": [],
        "historical_Lean_replay": "Reused unchanged exact-source evidence from route-a and earlier checkpoints; not rerun here",
        "external_machine_replay": False,
    }
    (HERE / "validation.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(protected)} protected baseline paths, {lock_entries} lock entries, "
          f"{len(scalar)} exact scalar checks, all guard regressions, and {len(replay)} finite Fisher replays.")


if __name__ == "__main__":
    main()
