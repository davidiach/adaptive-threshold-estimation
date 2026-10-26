"""Build and independently audit the separate full-713 development.

A passing component checkpoint is explicitly distinguished from the completed
theorem. The final proof must also typecheck against the recorded specification.
The specification and its complete local import closure are hash-locked. This
guard and its manifest are also included in the approved Tier 2 freeze.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SPECIFICATION = "lean/ThresholdHC/Uniform713/Specification.lean"
# Whole-file locks preserve the existing completed proof without moving definitions.
# The pinned Mathlib/toolchain and Statements.lean are also covered by FROZEN.sha256.
DEFINITION_SOURCES = {
    "lean/ThresholdHC/Statements.lean",
    "lean/ThresholdHC/Uniform713/Common.lean",
    "lean/ThresholdHC/Uniform713/Concentration.lean",
    "lean/ThresholdHC/Uniform713/Classifier.lean",
    "lean/ThresholdHC/Uniform713/Estimator.lean",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_specification_lock(manifest: dict, root: Path = ROOT) -> dict[str, str]:
    """Fail closed on a missing lock, changed definition, or changed specification."""
    dependencies = manifest.get("definition_sources_sha256", {})
    if set(dependencies) != DEFINITION_SOURCES:
        raise SystemExit("713 definition lock must cover every required source file")
    expected = {SPECIFICATION: manifest["specification_sha256"], **dependencies}
    for rel, digest in expected.items():
        path = root / rel
        if not path.is_file() or sha(path) != digest:
            raise SystemExit(f"713 specification/definition hash mismatch: {rel}; do not weaken the target")
    return expected


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--sequential", action="store_true")
    args = parser.parse_args()
    (ROOT / "results/uniform713_status.json").write_text(json.dumps({
        "valid": False, "full_theorem_complete": False,
        "error": "Verification has not completed successfully."
    }, indent=2) + "\n")
    manifest = json.loads((ROOT / "tools/uniform713_targets.json").read_text())
    modules = manifest["modules"]
    locked = check_specification_lock(manifest)
    sources = {m: LEAN / (m.replace(".", "/") + ".lean") for m in modules}
    hashes = {m: sha(p) for m, p in sources.items()}
    for module, path in sources.items():
        source = re.sub(r"/-[\s\S]*?-/|--[^\n]*", "", path.read_text(encoding="utf-8"))
        if re.search(r"\b(sorry|axiom|native_decide|implemented_by|extern|unsafe|opaque|run_cmd)\b"
                     r"|skipKernelTC|#exit|^\s*(elab|macro|syntax)\b", source, re.M):
            raise SystemExit(f"Forbidden proof escape in {path.relative_to(ROOT)}")
        declared = re.findall(r"^(?:@\[[^\]]+\]\s+)?(?:theorem|lemma|instance)\s+([\w']+)",
                              source, re.M)
        namespaces = re.findall(r"^namespace\s+([\w.]+)", source, re.M)
        if declared and len(namespaces) != 1:
            raise SystemExit(f"Audit registration needs explicit namespace handling: {module}")
        expected = {namespaces[0] + "." + n for n in declared} if declared else set()
        if expected != set(modules[module]):
            raise SystemExit(f"Public proof roots do not match audit registration: {module}")
    commands = [["lake", "build", m] for m in modules] if args.sequential else [
        ["lake", "build", *modules]]
    build_log = []
    for command in commands:
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        build_log.append(result.stdout + result.stderr)
        if result.returncode:
            (ROOT / "results/uniform713_build.log").write_text("\n".join(build_log), encoding="utf-8")
            raise SystemExit(f"713 build failed: {command}; see results/uniform713_build.log")
    (ROOT / "results/uniform713_build.log").write_text("\n".join(build_log), encoding="utf-8")
    names = [name for names in modules.values() for name in names]
    lines = [f"import {m}" for m in modules]
    full = manifest.get("full_theorem")
    if full:
        lines.append(f"example : ThresholdHC.Uniform713.FullBound713Statement := {full}")
        if full not in names:
            raise SystemExit("Full theorem must also be an audited root")
    lines.extend(f"#print axioms {name}" for name in names)
    audit = LEAN / ".audit/Uniform713.lean"
    audit.parent.mkdir(exist_ok=True)
    audit.write_text("\n".join(lines) + "\n", encoding="utf-8")
    result = subprocess.run(["lake", "env", "lean", str(audit.relative_to(LEAN))],
                            cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
    output = result.stdout + result.stderr
    (ROOT / "results/uniform713_audit.log").write_text(output, encoding="utf-8")
    reports = {}
    pattern = r"'([^']+)'\s+(depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, output, re.S):
        reports[match[1]] = [] if match[3] is None else [s.strip() for s in match[3].split(",") if s.strip()]
    unchanged = hashes == {m: sha(p) for m, p in sources.items()}
    lock_unchanged = locked == {rel: sha(ROOT / rel) for rel in locked}
    ok = (result.returncode == 0 and set(reports) == set(names) and unchanged
          and lock_unchanged
          and all(set(a) <= ALLOWED for a in reports.values()))
    complete = ok and full is not None
    status = dict(valid=ok, full_theorem_complete=complete, full_theorem=full,
                  audit_exit_code=result.returncode, root_count=len(reports),
                  expected_root_count=len(names), sources_unchanged_during_audit=unchanged,
                  specification_sha256=manifest["specification_sha256"],
                  definition_sources_sha256=manifest["definition_sources_sha256"],
                  specification_dependencies_unchanged_during_audit=lock_unchanged,
                  source_sha256=hashes, reports=reports)
    (ROOT / "results/uniform713_status.json").write_text(json.dumps(status, indent=2) + "\n")
    print(f"713 audit: valid={ok}, complete={complete}, roots={len(reports)}/{len(names)}")
    return 0 if ok and (complete or not args.require_complete) else 1


if __name__ == "__main__":
    raise SystemExit(main())
