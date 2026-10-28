"""Kernel-check the full distribution-blind upper theorem and its construction.

Lake rebuilds any stale prerequisite, so earlier baseline/Tier 6 and
critical-component runs only save time. The final proof must inhabit the
unchanged frozen specification. This audit does not certify the separate
critical rare-event upper theorem. Use --sequential on memory-limited runners.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

from verify_tier6 import ALLOWED, FORBIDDEN as TIER6_FORBIDDEN, strip_comments

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
REGISTRY = ROOT / "tools/blind_upper_components.json"
SPECIFICATION = "lean/ThresholdHC/BlindUpper/Specification.lean"
SPECIFICATION_SHA256 = "9531acd63300aa44359d293b84cc544d40977c6be79c0a87a1d24bcfe410ab15"
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
    r"(?:def|abbrev|structure|theorem|lemma|instance|inductive)\s+"
    r"([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)", re.M)
IMPORT = re.compile(r"^import\s+([\w.]+)\s*$", re.M)
# The frozen Tier 6 pattern misses the `admit` tactic, which is Lean's synonym
# for `sorry`. Audited sources also contain no string literals: strip_comments
# does not parse strings, so "/-" or "--" inside one could hide the code after
# it, and a printed string could forge an axiom report in the audit output.
FORBIDDEN = re.compile(TIER6_FORBIDDEN.pattern + r'|\badmit\b|"', TIER6_FORBIDDEN.flags)
# Unlike the frozen Tier 6 pattern, this also reads primed names such as foo'.
REPORT = re.compile(
    r"'(\S+?)'\s+(depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.S)
EXACT_TARGETS = {
    "ThresholdHC.BlindUpper.distribution_blind_upper":
        "ThresholdHC.BlindUpper.DistributionBlindUpperStatement",
}
EXTRA_DEPENDENCIES = ["ThresholdHC.Tier6.HardPair", "ThresholdHC.Tier6.AlgorithmNonempty",
                      "ThresholdHC.Tier6.RiskReduction"]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(module: str) -> Path:
    if not re.fullmatch(r"ThresholdHC(?:\.[A-Za-z_][A-Za-z_0-9]*)+", module):
        raise ValueError("Unexpected project module: " + module)
    return LEAN.joinpath(*module.split(".")).with_suffix(".lean")


def imports(source: str) -> list[str]:
    """Accept the registered one-module-per-line format, failing closed otherwise.

    Lean also accepts several modules on one import line. Silently ignoring such
    a line would omit dependencies from the source hashes and specification lock.
    """
    result = []
    for line in source.splitlines():
        if re.match(r"\s*import\b", line):
            match = re.fullmatch(r"\s*import[^\S\n]+([\w.]+)\s*", line)
            if match is None:
                raise ValueError("Unsupported import syntax: " + line.strip())
            result.append(match[1])
    return result


def validate_dependency_freeze(specification: Path, freeze: dict) -> None:
    dependencies = project_dependencies([specification]) - {specification}
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(dependencies)}
    if freeze.get("dependency_sha256") != actual:
        raise ValueError("Frozen specification dependency changed")


def validate_reports(output: str, returncode: int, expected: set[str]) -> dict[str, list[str]]:
    if returncode:
        raise ValueError("Lean audit exited unsuccessfully")
    if "declaration uses 'sorry'" in output:
        raise ValueError("Lean audit reported a declaration that uses sorry")
    reports: dict[str, list[str]] = {}
    for name, _kind, axioms in REPORT.findall(output):
        if name in reports:
            raise ValueError("Duplicate audit root: " + name)
        reports[name] = [a.strip() for a in axioms.split(",") if a.strip()]
    if set(reports) != expected:
        raise ValueError("Missing or unexpected audit roots")
    if any(set(axioms) - ALLOWED for axioms in reports.values()):
        raise ValueError("Disallowed transitive axiom")
    return reports


def validate_sources(registry: dict) -> tuple[list[Path], set[str]]:
    modules = registry["modules"]
    roots = registry["roots"]
    if len(modules) != len(set(modules)) or len(roots) != len(set(roots)):
        raise ValueError("Duplicate module or root")
    if registry["full_distribution_blind_upper_verified"] is not True or registry["full_critical_upper_verified"] is not False:
        raise ValueError("The registered full theorem is the distribution-blind upper only")
    if registry.get("exact_targets") != EXACT_TARGETS or not set(EXACT_TARGETS) <= set(roots):
        raise ValueError("Missing or changed frozen full-theorem target")
    if registry["specification_path"] != SPECIFICATION or registry["specification_sha256"] != SPECIFICATION_SHA256:
        raise ValueError("Frozen specification registration changed")
    if sha(ROOT / SPECIFICATION) != SPECIFICATION_SHA256:
        raise ValueError("Frozen distribution-blind specification changed")
    freeze = json.loads((ROOT / "tools/blind_upper_specification_freeze.json").read_text(encoding="utf-8"))
    if freeze.get("source") != SPECIFICATION or freeze.get("sha256") != SPECIFICATION_SHA256:
        raise ValueError("Frozen specification registration changed")
    validate_dependency_freeze(ROOT / SPECIFICATION, freeze)
    if registry["extra_dependency_builds"] != EXTRA_DEPENDENCIES:
        raise ValueError("Unregistered prerequisite build")
    paths = [module_path(m) for m in modules]
    actual = set((LEAN / "ThresholdHC/ObservableSimulation").glob("*.lean"))
    actual.update((LEAN / "ThresholdHC/BlindUpper").glob("*.lean"))
    if set(paths) != actual:
        raise ValueError("Unregistered or missing upper-construction source")
    declared = []
    seen = set()
    for module, path in zip(modules, paths):
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        namespace = module.rsplit(".", 1)[0] + "."
        declared.extend(namespace + name for name in DECLARATION.findall(source))
        for dependency in imports(source):
            if dependency in modules and dependency not in seen:
                raise ValueError("Component dependency order is invalid: " + dependency)
        seen.add(module)
    if len(declared) != len(roots) or set(declared) != set(roots):
        raise ValueError("Public declaration coverage mismatch")
    return paths, set(roots)


def project_dependencies(paths: list[Path]) -> set[Path]:
    """Protect every local source imported transitively by a checked component."""
    found: set[Path] = set()
    pending = list(paths)
    while pending:
        path = pending.pop()
        if path in found:
            continue
        source = strip_comments(path.read_text(encoding="utf-8"))
        found.add(path)
        for dependency in imports(source):
            if dependency.startswith("ThresholdHC."):
                pending.append(module_path(dependency))
            elif dependency != "Mathlib" and not dependency.startswith("Mathlib."):
                raise ValueError("Unexpected external import: " + dependency)
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--sequential", action="store_true")
    args = parser.parse_args()
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    paths, expected = validate_sources(registry)
    protected = project_dependencies(paths) | {
        Path(__file__).resolve(), REGISTRY, ROOT / "tools/verify_tier6.py",
        ROOT / "tools/blind_upper_specification_freeze.json",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/blind-upper-components" / datetime.now(
        timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    status = {
        "valid": False,
        "scope": registry["scope"],
        "full_distribution_blind_upper_verified": False,
        "full_critical_upper_verified": False,
        "observable_simulation_law_verified": False,
        "calibrated_call_array_bounds_verified": False,
        "independent_seed_stream_law_verified": False,
        "observable_controller_verified": False,
        "controller_population_cost_and_output_identities_verified": False,
        "exact_targets": EXACT_TARGETS,
        "exact_targets_checked": 0,
        "specification_sha256": SPECIFICATION_SHA256,
        "source_sha256": hashes,
        "commands": [],
    }
    status_path = output / "status.json"
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    audit = LEAN / ".audit/BlindUpperComponents.lean"
    audit.parent.mkdir(exist_ok=True)
    audit.write_text("".join("import " + m + "\n" for m in registry["modules"]) + "\n" +
                     "".join(f"example : {target} := {declaration}\n"
                             for declaration, target in EXACT_TARGETS.items()) + "\n" +
                     "".join("#print axioms " + r + "\n" for r in sorted(expected)), encoding="utf-8")
    # Lake rebuilds any stale transitive import, so hashed sources are the compiled ones.
    modules = registry["extra_dependency_builds"] + registry["modules"]
    commands = [["lake", "build", m] for m in modules] if args.sequential else [["lake", "build", *modules]]
    commands.append(["lake", "env", "lean", str(audit.relative_to(LEAN))])
    for i, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        text = result.stdout + result.stderr
        (output / f"{i + 1:02d}.log").write_text(text, encoding="utf-8")
        status["commands"].append({"command": command, "exit_code": result.returncode})
        status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        print(f"{command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(text, flush=True)
            return result.returncode
    status["axioms"] = validate_reports(text, result.returncode, expected)
    validate_sources(registry)
    if any(sha(ROOT / rel) != digest for rel, digest in hashes.items()):
        raise ValueError("Protected source changed during audit")
    status.update(valid=True, audited_modules=len(paths), audited_declarations=len(expected),
                  observable_simulation_law_verified=True, calibrated_call_array_bounds_verified=True,
                  independent_seed_stream_law_verified=True, observable_controller_verified=True,
                  controller_population_cost_and_output_identities_verified=True,
                  full_distribution_blind_upper_verified=True, exact_targets_checked=len(EXACT_TARGETS))
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"valid": True, "modules": len(paths), "axiom_roots": len(expected),
                      "full_distribution_blind_upper_verified": True, "evidence": str(output)}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
