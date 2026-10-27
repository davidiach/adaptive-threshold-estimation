"""Replay existing numerical/integrity gates on a byte snapshot, not published results.

No new sampling, tuning, or held-out selection. The snapshot includes current
working-tree bytes for tracked files, rather than assuming HEAD is the workspace.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEST = ROOT.parent / "route-a-baseline-snapshot"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT).decode("utf-8").strip()


def main():
    if DEST.exists():
        raise SystemExit(f"Refusing to overwrite an existing snapshot: {DEST}")
    DEST.mkdir()
    before = git("rev-parse", "HEAD")
    files = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0")
    hashes = {}
    for rel in filter(None, files):
        source = ROOT / rel
        if not source.is_file():
            continue
        target = DEST / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        data = source.read_bytes()
        target.write_bytes(data)
        hashes[rel] = hashlib.sha256(data).hexdigest()
    metadata = dict(head_before=before, head_after=git("rev-parse", "HEAD"),
                    status=git("status", "--short"), snapshot=str(DEST), files=hashes,
                    python=sys.version, source="current tracked working-tree bytes")
    (HERE / "baseline-snapshot.json").write_text(json.dumps(metadata, indent=2)+"\n")
    commands = [
        ["tools/verify_inputs.py"], ["tools/verify_experiment_lock.py"],
        ["tools/freeze.py", "--verify"], ["tools/check_targets_numeric.py"],
        ["tools/check_targets2_numeric.py"],
        ["-m", "unittest", "discover", "-s", "tools", "-p", "test_*.py", "-v"],
        ["tools/check_power_bracket.py"], ["proposals/constants/bias_audit.py"],
        ["proposals/constants/uniform_constant_checks.py"],
        ["constants/score_constants.py", "constants/candidate_theory.json"],
        ["constants/score_constants.py", "constants/candidate_finite_grid.json"],
        ["constants/score_constants.py", "constants/candidate.json"],
        ["benchmark/verify_real.py"],
    ]
    logdir = HERE / "baseline-logs"
    logdir.mkdir(exist_ok=True)
    records = []
    env = dict(os.environ, PYTHONUTF8="1")
    bundled = ROOT / ".runtime/python"
    if bundled.is_dir():
        env["PYTHONPATH"] = str(bundled) + os.pathsep + env.get("PYTHONPATH", "")
    for i, args in enumerate(commands):
        start = time.time()
        proc = subprocess.run([sys.executable, *args], cwd=DEST, env=env,
                              capture_output=True, text=True, encoding="utf-8")
        logfile = logdir / f"{i+1:02d}.log"
        logfile.write_text(proc.stdout+proc.stderr, encoding="utf-8")
        record = dict(command=[sys.executable, *args], exit=proc.returncode,
                      seconds=round(time.time()-start, 3), log=str(logfile.relative_to(HERE)))
        records.append(record)
        print(f"{i+1:02d} exit={proc.returncode}: {' '.join(args)}", flush=True)
        (HERE / "baseline-checks.json").write_text(json.dumps(records, indent=2)+"\n")
    # These exact lock checks are read-only and do not need a Lean rebuild.
    sys.path.insert(0, str(DEST / "tools"))
    import verify_tier3, verify_tier4
    for mod, name in [(verify_tier3, "tier3"), (verify_tier4, "tier4")]:
        manifest = json.loads((DEST / mod.MANIFEST).read_text())
        locked = mod.check_locks(manifest, DEST)
        print(f"{name}: {len(locked)} locked files verified", flush=True)
    return max(r["exit"] for r in records)


if __name__ == "__main__":
    raise SystemExit(main())
