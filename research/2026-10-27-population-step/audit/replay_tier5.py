"""Isolated current-source Tier5 replay using unchanged repository validators.

Does not overwrite results/tier5_status.json or lean/.audit/Tier5.lean.
Builds are cache-aware. The nine exact statement wrappers are freshly elaborated.
The original stored status is reported only as checkpoint evidence.
"""
from pathlib import Path
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "lean"
sys.path.insert(0, str(ROOT / "tools"))
import verify_tier5 as guard


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    record = {"valid": False, "complete": False,
              "utc": datetime.now(timezone.utc).isoformat(),
              "python": platform.python_version(),
              "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "script_sha256": sha(Path(__file__))}
    manifest = json.loads((ROOT / guard.MANIFEST).read_text(encoding="utf-8"))
    locked = guard.check_locks(manifest, ROOT)
    paths = sorted(guard.SOURCE.glob("*.lean"))
    modules = [".".join(p.relative_to(LEAN).with_suffix("").parts) for p in paths]
    roots = [name for p in paths for name in guard.declarations(p)]
    assert len(roots) == len(set(roots))
    targets = manifest["targets"]
    assert all(t["theorem"] in roots for t in targets), "Incomplete actual Tier5 targets"
    closure = set()
    for module in modules:
        closure |= guard.local_import_closure(module, ROOT)
    source_before = {rel: sha(ROOT / rel) for rel in sorted(closure)}
    old_path = ROOT / "results/tier5_status.json"
    old = json.loads(old_path.read_text(encoding="utf-8"))
    old_hash_mismatches = [rel for field in ("source_sha256", "locked_sha256")
                           for rel, digest in old[field].items()
                           if not (ROOT / rel).exists() or sha(ROOT / rel) != digest]
    record.update(original_status_sha256=sha(old_path),
                  original_recorded_valid=old.get("valid"),
                  original_recorded_complete=old.get("complete"),
                  original_hash_mismatches=old_hash_mismatches,
                  source_sha256_before=source_before, locked_sha256=locked,
                  local_dependency_source_count=len(source_before))
    lines = ["import " + module for module in modules]
    lines += ["namespace PopulationStepTier5Audit"]
    exact_roots = []
    for target in targets:
        name = "audit_" + target["theorem"].rsplit(".", 1)[-1]
        lines.append(f"theorem {name} : {target['statement']} := {target['theorem']}")
        exact_roots.append("PopulationStepTier5Audit." + name)
    lines += ["end PopulationStepTier5Audit"]
    expected = set(roots + exact_roots)
    lines += ["#print axioms " + name for name in sorted(expected)]
    audit = HERE / "CurrentTier5Audit.lean"
    audit.write_text("\n".join(lines)+"\n", encoding="utf-8")
    record.update(targets=targets, expected_roots=len(expected),
                  audit_source_sha256=sha(audit), commands=[])
    env = dict(os.environ, ELAN_HOME=str(ROOT / ".runtime/elan"), PYTHONUTF8="1")
    lake = str(ROOT / ".runtime/elan/bin/lake.exe")
    for label, command in [
        ("build", [lake, "build", *modules]),
        ("audit", [lake, "env", "lean", str(audit)]),
    ]:
        started = time.monotonic()
        run = subprocess.run(command, cwd=LEAN, env=env, capture_output=True,
                             text=True, encoding="utf-8", timeout=900)
        output = run.stdout + run.stderr
        (HERE / f"tier5_{label}.log").write_text(output, encoding="utf-8")
        record["commands"].append({"command": command, "cwd": str(LEAN),
                                   "exit_code": run.returncode,
                                   "seconds": time.monotonic()-started})
        if run.returncode:
            (HERE / "tier5_replay.json").write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8")
            raise RuntimeError(f"Tier5 {label} failed; see isolated log")
    reports = guard.parse_reports(output)
    source_after = {rel: sha(ROOT / rel) for rel in sorted(closure)}
    unchanged = source_before == source_after and locked == guard.check_locks(manifest, ROOT)
    unchanged = unchanged and paths == sorted(guard.SOURCE.glob("*.lean"))
    ok = guard.valid_audit(run.returncode, reports, expected, unchanged)
    record.update(valid=ok, complete=ok, reports=reports, actual_roots=len(reports),
                  axiom_union=sorted({a for xs in reports.values() for a in xs}),
                  source_sha256_after=source_after,
                  sources_and_locks_unchanged=unchanged,
                  original_status_unchanged=sha(old_path)==record["original_status_sha256"],
                  build_kind="cache-aware module builds; fresh exact-type and axiom audit")
    (HERE / "tier5_replay.json").write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({k: record[k] for k in ["valid", "complete", "actual_roots", "expected_roots",
                                          "axiom_union", "original_hash_mismatches"]}))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
