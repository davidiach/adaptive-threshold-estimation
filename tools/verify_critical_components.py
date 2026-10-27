"""Check the scoped critical-proof components; never certify the full theorem.

This extension does not change existing frozen targets or scores. It reuses the
frozen Tier 6 source and transitive-axiom guards. Specifications were introduced
with these proofs, not retrospectively described as a pre-proof freeze.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

from verify_tier6 import ALLOWED, DECLARATION, FORBIDDEN, REPORT, strip_comments

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
SOURCE = LEAN / "ThresholdHC/CriticalEntropy"
MODULES = ("Packing", "CommonPoint", "Specification")
NAMESPACE = "ThresholdHC.CriticalEntropy."
ROOTS = {
    NAMESPACE + name for name in (
        "sum_event_mass_le_overlap", "event_packing", "overlap_bound",
        "entropy_of_packing", "entropy_of_gap_count", "finite_common_point",
        "common_point_of_finite_mixtures", "EntropyPackingStatement", "CommonPointStatement",
    )
}


def validate_reports(output: str, returncode: int) -> dict[str, list[str]]:
    if returncode != 0:
        raise ValueError("Lean audit exited unsuccessfully")
    reports: dict[str, list[str]] = {}
    for name, _kind, axioms in REPORT.findall(output):
        if name in reports:
            raise ValueError("Duplicate audit root: " + name)
        reports[name] = [a.strip() for a in axioms.split(",") if a.strip()]
    if set(reports) != ROOTS:
        raise ValueError("Missing or unexpected audit roots")
    if any(set(axioms) - ALLOWED for axioms in reports.values()):
        raise ValueError("Disallowed transitive axiom")
    return reports


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    output = args.output_dir or ROOT / ".runtime/critical-components" / datetime.now(
        timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    sources = sorted(SOURCE.glob("*.lean"))
    expected_sources = {name + ".lean" for name in (*MODULES, "Audit")}
    if {p.name for p in sources} != expected_sources:
        raise ValueError("Unexpected or missing component module")
    declared = []
    for path in sources:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        imports = re.findall(r"^import\s+([\w.]+)\s*$", source, re.M)
        allowed_imports = {"Mathlib"} | {NAMESPACE + name for name in MODULES}
        if any(module not in allowed_imports for module in imports):
            raise ValueError("Unregistered component import in " + path.name)
        declared.extend(NAMESPACE + name for name in DECLARATION.findall(source))
    if len(declared) != len(ROOTS) or set(declared) != ROOTS:
        raise ValueError("Public declaration coverage mismatch")
    protected = sources + [Path(__file__).resolve(), ROOT / "tools/verify_tier6.py",
                           LEAN / "lean-toolchain", LEAN / "lake-manifest.json"]
    hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in protected}
    status = {
        "valid": False,
        "scope": "Entropy event packing and abstract compact convex common-point implication",
        "full_critical_minimax_theorem_verified": False,
        "base_cost_theorem_verified": False,
        "finite_gap_sign_testing_theorem_verified": False,
        "specifications_frozen_before_proofs": False,
        "source_sha256": hashes,
        "commands": [],
    }
    status_path = output / "status.json"
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    build = LEAN / ".lake/build/lib/lean/ThresholdHC/CriticalEntropy"
    build.mkdir(parents=True, exist_ok=True)
    commands = [["lake", "env", "lean", "-o", str(build / (name + ".olean")),
                 "ThresholdHC/CriticalEntropy/" + name + ".lean"] for name in MODULES]
    commands.append(["lake", "env", "lean", "ThresholdHC/CriticalEntropy/Audit.lean"])
    for index, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True,
                                encoding="utf-8")
        text = result.stdout + result.stderr
        (output / f"{index + 1:02d}.log").write_text(text, encoding="utf-8")
        status["commands"].append({"command": command, "exit_code": result.returncode})
        status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        if result.returncode:
            print(text)
            return result.returncode
    status["axioms"] = validate_reports(text, result.returncode)
    if any(hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest
           for rel, digest in hashes.items()):
        raise ValueError("Sources changed during audit")
    status.update(valid=True, exact_component_targets=2, audited_declarations=len(ROOTS))
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"valid": True, "exact_component_targets": 2,
                      "audited_declarations": len(ROOTS), "evidence": str(output),
                      "full_critical_minimax_theorem_verified": False}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
