"""Final read-only baseline comparison and fresh additive formal/analytic replay.

Writes only this task's diagnostics and its new Lean bridge diagnostics.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    baseline = json.loads((HERE / "baseline-snapshot.json").read_text())
    checked = []
    for rel, digest in baseline["files"].items():
        if rel.startswith(("lean/", "tools/", "inputs/", "constants/", "benchmark/", "results/")) or rel.endswith("FROZEN.sha256"):
            if sha(ROOT / rel) != digest:
                raise RuntimeError("Pre-existing research/evidence changed: " + rel)
            checked.append(rel)
    if (ROOT / "paper/paper.tex").read_bytes() != (ROOT / "inputs/next-phase/baseline/Adaptive_Threshold_v4/source/paper.tex").read_bytes():
        raise RuntimeError("Imported paper changed")
    sys.path.insert(0, str(ROOT / "tools"))
    import verify_tier4
    guarded = []
    for path in (ROOT / "lean/ThresholdHC/ResearchRouteA").glob("*.lean"):
        if verify_tier4.FORBIDDEN.search(verify_tier4.strip_comments(path.read_text(encoding="utf-8"))):
            raise RuntimeError("Forbidden syntax in new proof: " + str(path))
        guarded.append(str(path.relative_to(ROOT)))
    env = dict(os.environ, PYTHONUTF8="1")
    elan = ROOT / ".runtime/elan"
    if elan.is_dir():
        env["ELAN_HOME"] = str(elan)
        env["PATH"] = str(elan / "bin") + os.pathsep + env.get("PATH", "")
    records = []
    for args, name in [(["research/2026-10-27-route-a/check_construction.py"], "construction"),
                       (["lean/ThresholdHC/ResearchRouteA/verify.py"], "formal")]:
        proc = subprocess.run([sys.executable, *args], cwd=ROOT, env=env,
                              text=True, encoding="utf-8", capture_output=True)
        (HERE / f"acceptance-{name}.log").write_text(proc.stdout+proc.stderr, encoding="utf-8")
        records.append(dict(command=[sys.executable, *args], exit_code=proc.returncode))
        if proc.returncode:
            raise RuntimeError(proc.stdout+proc.stderr)
    # Both sources and review identities are included. The records are evidence
    # for these exact bytes, independent of concurrent unrelated HEAD changes.
    sources = list(HERE.glob("*.tex")) + list(HERE.glob("*.md")) + list(HERE.glob("*.py"))
    sources += list((ROOT / "lean/ThresholdHC/ResearchRouteA").glob("*.lean"))
    sources += [ROOT / "lean/ThresholdHC/ResearchRouteA/SPEC_LOCK_v1.json",
                ROOT / "lean/ThresholdHC/ResearchRouteA/verify.py"]
    status = dict(valid=True, baseline_files_unchanged=len(checked),
                  broad_frozen_guard_sources=guarded, commands=records,
                  head_at_replay=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip(),
                  source_sha256={str(p.relative_to(ROOT)).replace("\\", "/"):sha(p) for p in sorted(sources)},
                  independent_external_machine_replay=False,
                  main_theorem_status="paper proof with agent review; not Lean-checked")
    (HERE / "acceptance.json").write_text(json.dumps(status, indent=2)+"\n")
    print(f"PASS: {len(checked)} pre-existing source/evidence files unchanged; broad proof guards; fresh exact-type and axiom replay; 18 exact finite-prefix checks.")


if __name__ == "__main__":
    main()
