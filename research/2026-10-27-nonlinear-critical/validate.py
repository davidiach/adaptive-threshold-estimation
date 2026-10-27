"""Replay paper-artifact checks into a fresh directory; never overwrite evidence.

This does not verify the statistical proof in Lean or infer it from finite cases.
The exact continuum/all-policy claims are supported by the paper and reviews.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DOCS = {
    "README.md", "docs/process/REPORT.md", "docs/process/RUNLOG.md",
    "docs/RESULTS.md", "docs/VERIFY.md", "paper/UPDATES.md",
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def require(value, message):
    if not value:
        raise RuntimeError(message)


def scalar_checks():
    checks = {
        "prefix_kl": F(64, 3) / 1024 == F(1, 48),
        "prefix_pinsker": F(1, 96) < F(1, 64),
        "sign_window_mass": 1 - F(2, 10) - F(1, 8) - F(1, 4) > F(1, 4),
        "variance_floor": F(3, 4) * F(31, 32) ** 2 >= F(2, 3),
        "moment_variance_bridge": 1 + F(3, 8) * F(65, 64) ** 2 <= F(3, 2),
        "restart_envelope": F(513) / F(2, 3) + 512 <= 1282,
        "restart_error": F(32, 512) < F(1, 10),
        "capped_bad_mass": 64 + 4 / F(2, 3) == 70,
        "annulus_product_constant": F(16, 3) * 1282 * 4 < 30000,
        "component_variance": 1 + 4 * F(1, 4) / (1 - F(1, 4)) == F(7, 3),
        "affine_rms_squared_envelope": F(17, 2) * 16 < 144,
        "affine_saddle_rms_envelope": F(17, 2) < 9,
        "population_hellinger": 2 * F(1, 16) == F(1, 8),
        "population_tv_squared": 2 * F(1, 8) == F(1, 4),
        "testing_rms_squared": F(1, 2) / 8 == F(1, 16),
        "upper_second_moment": F(35, 16) + F(85, 16) / 7 == F(165, 56),
        "upper_work": 2 * F(225, 2) * 6 == 1350,
    }
    require(all(checks.values()), "Scalar diagnostic failed: " + repr(checks))
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = args.output_dir or HERE / "replays" / stamp
    out.mkdir(parents=True, exist_ok=False)
    baseline = json.loads((HERE / "BASELINE.json").read_text(encoding="utf-8"))
    protected, other_changes = [], []
    for rel, expected in baseline["sha256"].items():
        p = ROOT / rel
        current = sha(p) if p.is_file() else None
        foreign = rel.startswith(("research/2026-10-27-population-step/",
                                  "research/2026-10-27-nonlinear-population/"))
        foreign = foreign or "Tier5" in rel or "tier5" in rel
        # Frozen Tier5 targets and tools are still protected despite concurrent proofs.
        frozen_or_tool = rel.endswith("FROZEN.sha256") or rel.startswith("tools/")
        if rel not in DOCS and (not foreign or frozen_or_tool):
            require(current == expected, "Protected starting bytes changed: " + rel)
            protected.append(rel)
        elif current != expected:
            other_changes.append({"path": rel, "baseline": expected, "current": current,
                                  "task_document": rel in DOCS})

    old_lock_entries = 0
    for name in ("FROZEN.sha256", "TIER3_FROZEN.sha256", "TIER4_FROZEN.sha256", "TIER5_FROZEN.sha256"):
        for line in (ROOT / name).read_text(encoding="utf-8").splitlines():
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            digest, rel = line.split(maxsplit=1)
            require(sha(ROOT / rel.strip()) == digest, "Freeze mismatch: " + rel)
            old_lock_entries += 1
    json_locks = (
        ("lean/ThresholdHC/ResearchRouteA/SPEC_LOCK_v1.json", ROOT),
        ("research/2026-10-27-critical-two/CHECKPOINT_LOCK_v1.json", ROOT),
        ("research/2026-10-27-minimax-audit/PAPER_CHECKPOINT_LOCK_v1.json",
         ROOT / "research/2026-10-27-minimax-audit"),
        ("research/2026-10-27-minimax-audit/formal/MODEL_EXTENSION_LOCK_v1.json",
         ROOT / "research/2026-10-27-minimax-audit/formal"),
    )
    for lock_name, base in json_locks:
        lock = json.loads((ROOT / lock_name).read_text(encoding="utf-8"))
        mapping = lock.get("locked_sha256", lock.get("sha256"))
        require(bool(mapping), "Missing lock mapping: " + lock_name)
        for rel, digest in mapping.items():
            require(sha(base / rel) == digest, "Prior checkpoint mismatch: " + rel)
            old_lock_entries += 1

    lock = json.loads((HERE / "CHECKPOINT_LOCK_v1.json").read_text(encoding="utf-8"))
    for rel, digest in lock["sha256"].items():
        require(sha(HERE / rel) == digest, "Current paper lock mismatch: " + rel)
    inputs = set(re.findall(r"\\input\{([^}]+)\}", (HERE / "unrestricted.tex").read_text()))
    require(inputs == set(lock["sha256"]) - {"unrestricted.tex"}, "Incomplete TeX input closure")
    for review in ("review.md", "second-review.md"):
        content = (HERE / review).read_text(encoding="utf-8")
        require(all(h in content for h in lock["sha256"].values()), "Review identities missing: " + review)
    compilation = json.loads((HERE / "compilation.json").read_text(encoding="utf-8"))
    require(compilation["kind"] == "success" and compilation["source_sha256"] == lock["sha256"],
            "Compilation bundle differs from final paper")

    env = dict(os.environ, PYTHONUTF8="1")
    records = []
    commands = (
        ("freeze", ["tools/freeze.py", "--verify"]),
        ("inputs", ["tools/verify_inputs.py"]),
        ("regressions", ["-m", "unittest", "discover", "-s", "tools", "-p", "test_*.py", "-v"]),
        ("finite-prefix", [str(HERE / "check_prefix.py"), "--output", str(out / "check_prefix_results.json")]),
    )
    for name, argv in commands:
        start = time.monotonic()
        proc = subprocess.run([sys.executable, *argv], cwd=ROOT, env=env,
                              capture_output=True, text=True, encoding="utf-8")
        (out / (name + ".log")).write_text(proc.stdout + proc.stderr, encoding="utf-8")
        records.append({"command": [sys.executable, *argv], "exit_code": proc.returncode,
                        "seconds": time.monotonic() - start})
        require(proc.returncode == 0, "Check failed: " + name + "\n" + proc.stdout + proc.stderr)
    require(sha(out / "check_prefix_results.json") == sha(HERE / "check_prefix_results.json"),
            "Exact finite-prefix replay differs from recorded result")
    prefix = json.loads((out / "check_prefix_results.json").read_text())
    sources = sorted(p for p in HERE.iterdir() if p.suffix in (".tex", ".md", ".py"))
    sources += [ROOT / p for p in sorted(DOCS)]
    result = {
        "valid": True, "timestamp_utc": stamp,
        "evidence_scope": "Paper bundle, preservation and exact finite diagnostics; no Lean proof of new theorem",
        "head_at_replay": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip(),
        "baseline_head": baseline["head"],
        "protected_baseline_files_unchanged": len(protected),
        "prior_lock_entries_verified": old_lock_entries,
        "other_baseline_changes": other_changes,
        "paper_lock_sha256": sha(HERE / "CHECKPOINT_LOCK_v1.json"),
        "paper_source_sha256": lock["sha256"],
        "compilation_bundle_matches": True,
        "scalar_checks": scalar_checks(), "commands": records,
        "population_prefix_cases": prefix["population_cases"],
        "sufficiency_cases": prefix["sufficiency_cases"],
        "finite_prefix_replay_exact_match": True,
        "source_sha256": {p.relative_to(ROOT).as_posix(): sha(p) for p in sources},
        "new_Lean_targets": [],
        "historical_Lean_evidence": "Unchanged pinned sources and prior evidence reused; not rerun here",
        "external_replay": "No independent-machine replay of new research diagnostic or theorem",
        "output_directory": str(out),
    }
    (out / "validation.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(protected)} protected paths, {old_lock_entries} prior lock entries, "
          f"{len(result['scalar_checks'])} scalar checks, all guard regressions, "
          f"{prefix['population_cases']} prefix + {prefix['sufficiency_cases']} sufficiency cases.")
    print(out / "validation.json")


if __name__ == "__main__":
    main()
