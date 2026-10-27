"""Replay only this additive bridge; never overwrite baseline verification records."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = [
    "ThresholdHC.ResearchRouteA.separate_moment_bounds",
    "ThresholdHC.ResearchRouteA.uniform_family_bounds",
    "ThresholdHC.ResearchRouteA.independent_constant_observations",
    "ThresholdHC.ResearchRouteA.deterministic_gap_model",
    "ThresholdHC.ResearchRouteA.deterministic_gap_separate_bounds",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure(files):
    found = set()
    pending = list(files)
    while pending:
        path = pending.pop()
        if path in found:
            continue
        found.add(path)
        for module in re.findall(r"^import\s+([\w.]+)", path.read_text(encoding="utf-8"), re.M):
            if module.startswith("ThresholdHC"):
                pending.append(LEAN / (module.replace(".", "/") + ".lean"))
    return found


def main():
    status = {"valid": False, "complete": False, "new_mathematical_advance": False}
    status_path = HERE / "status.json"
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    lock_path = HERE / "SPEC_LOCK_v1.json"
    lock = json.loads(lock_path.read_text(encoding="utf-8"))
    actual_closure = {str(p.relative_to(ROOT)).replace("\\", "/") for p in
                      closure([HERE / "SeparateBoundsSpec.lean"])}
    if actual_closure != set(lock["specification_closure"]):
        raise RuntimeError("Specification closure mismatch")
    for rel, digest in lock["locked_sha256"].items():
        if sha(ROOT / rel) != digest:
            raise RuntimeError("Locked source changed: " + rel)
    all_sources = closure([HERE / "Audit.lean"])
    snapshots = {str(p.relative_to(ROOT)).replace("\\", "/"): sha(p)
                 for p in sorted(all_sources)}
    submitted = [HERE / name for name in
                 ["SeparateBoundsSpec.lean", "SeparateBounds.lean", "Sanity.lean", "Audit.lean"]]
    declared = []
    for path in submitted:
        source = re.sub(r"/-[\s\S]*?-/|--[^\n]*", "", path.read_text(encoding="utf-8"))
        if re.search(r"\b(sorry|axiom|native_decide|implemented_by|extern|unsafe|opaque|run_cmd)\b"
                     r"|skipKernelTC|#exit|^\s*(elab|macro|syntax)\b", source, re.M):
            raise RuntimeError("Forbidden proof escape: " + str(path))
        declared += ["ThresholdHC.ResearchRouteA." + name for name in
                     re.findall(r"^(?:theorem|lemma|instance)\s+([\w']+)", source, re.M)]
    if set(declared) != set(TARGETS) or len(declared) != len(TARGETS):
        raise RuntimeError("Public proof root coverage mismatch")
    env = os.environ.copy()
    elan = ROOT / ".runtime/elan"
    if elan.exists():
        env["ELAN_HOME"] = str(elan)
        env["PATH"] = str(elan / "bin") + os.pathsep + env.get("PATH", "")
    commands = [["lake", "build", "ThresholdHC.ResearchRouteA.Sanity"],
                ["lake", "env", "lean", "ThresholdHC/ResearchRouteA/Audit.lean"]]
    results = []
    for index, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, env=env, capture_output=True,
                                text=True, encoding="utf-8")
        output = result.stdout + result.stderr
        (HERE / ("build.log" if index == 0 else "audit.log")).write_text(output, encoding="utf-8")
        results.append({"command": command, "cwd": str(LEAN), "exit_code": result.returncode})
        if result.returncode:
            status.update(commands=results)
            status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
            print(output)
            return result.returncode
    reports = {name: re.findall(r"[\w.]+", axioms) for name, axioms in
               re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)}
    if set(reports) != set(TARGETS):
        raise RuntimeError("Missing or unexpected audit roots")
    if any(set(axioms) - ALLOWED for axioms in reports.values()):
        raise RuntimeError("Disallowed transitive axiom")
    if any(sha(ROOT / rel) != digest for rel, digest in snapshots.items()):
        raise RuntimeError("Sources changed during audit")
    if any(sha(ROOT / rel) != digest for rel, digest in lock["locked_sha256"].items()):
        raise RuntimeError("Lock changed during audit")
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                            capture_output=True, text=True, check=True).stdout.strip()
    status.update(valid=True, complete=True, status="Lean-checked against a specified target",
                  scope="Conditional observation-kernel separate-supremum bridge; no fresh-coin realization",
                  source_commit=commit, commands=results, specification_lock_sha256=sha(lock_path),
                  specification_sha256=sha(HERE / "SeparateBoundsSpec.lean"),
                  source_sha256=snapshots, root_count=len(TARGETS), reports=reports,
                  sources_unchanged_during_audit=True)
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: status[key] for key in
                      ["valid", "complete", "root_count", "specification_sha256"]}, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
