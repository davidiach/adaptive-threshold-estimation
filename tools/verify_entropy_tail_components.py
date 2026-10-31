"""Audit the arbitrary-law quantile comparison and deterministic ingredients.

Recompile the entire local dependency closure with the pinned Lean toolchain,
check the two frozen targets, and inspect every new declaration's transitive
axioms. This does not certify the statistical entropy-tail upper/lower bounds.
Evidence is written to a fresh .runtime directory, never a published result.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, imports, module_path, project_dependencies, sha,
    strip_comments, validate_dependency_freeze, validate_reports,
)

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
SOURCE = LEAN / "ThresholdHC/EntropyTailQuantile"
PREFIX = "ThresholdHC.EntropyTailQuantile."
MODULES = (
    "CostEntropy", "CostEntropySeries", "Model", "Specification", "QuantileAlgebra",
    "QuantileThreshold", "QuantileSplit", "MeasureEntropy", "QuantileSplitFull",
    "QuantileFeasible", "TailModulus", "BandGeometry", "ScaleSeparated",
    "CutDecomposition", "EntropyMixture", "EntropyMoment", "QuantileTailBound",
    "QuantileRootBound", "QuantileCoreBound", "QuantileComparison",
)
FROZEN = {
    "lean/ThresholdHC/EntropyTailQuantile/Model.lean":
        "9ace9b713b268d085c6eb281c424410987dfb37177e704d4b5c6e4c7fcb5f5c9",
    "lean/ThresholdHC/EntropyTailQuantile/Specification.lean":
        "ef13e8b2117cc2760d7553a023b39d84cd5482a97e26c304eac417f172998a6e",
}
EXACT_TARGETS = {
    PREFIX + "quantile_split": PREFIX + "QuantileSplitStatement",
    PREFIX + "quantile_comparison": PREFIX + "QuantileComparisonStatement",
}
SCOPE = (
    "Arbitrary probability laws on positive gaps up to one half; fractional boundary "
    "atoms; finite core entropy; K <= Q <= (1+2*sqrt(2))*K; saturation when "
    "B^(-1/2) >= the quantile threshold. All positive budgets and rho in (0,1/4]. "
    "No statistical minimax upper or lower theorem is certified by this audit."
)


def validate_sources() -> tuple[list[Path], set[str]]:
    freeze = json.loads((ROOT / "tools/entropy_tail_quantile_specification_freeze.json").read_text(encoding="utf-8"))
    if freeze["source_sha256"] != FROZEN or any(sha(ROOT / p) != h for p, h in FROZEN.items()):
        raise ValueError("Frozen entropy-tail model or specification changed")
    validate_dependency_freeze(SOURCE / "Specification.lean", freeze)
    paths = [module_path(PREFIX + m) for m in MODULES]
    if set(paths) != set(SOURCE.glob("*.lean")):
        raise ValueError("Missing or unregistered entropy-tail module")
    roots: list[str] = []
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        roots.extend(PREFIX + name for name in DECLARATION.findall(source))
    if len(roots) != len(set(roots)) or not set(EXACT_TARGETS) <= set(roots):
        raise ValueError("Duplicate or missing declaration root")
    return paths, set(roots)


def dependency_order(paths: list[Path]) -> list[Path]:
    ordered: list[Path] = []
    seen: set[Path] = set()
    active: set[Path] = set()

    def visit(path: Path) -> None:
        if path in active:
            raise ValueError("Cyclic local imports")
        if path in seen:
            return
        active.add(path)
        for name in imports(strip_comments(path.read_text(encoding="utf-8"))):
            if name.startswith("ThresholdHC."):
                visit(module_path(name))
            elif name != "Mathlib" and not name.startswith("Mathlib."):
                raise ValueError("Unexpected external import: " + name)
        active.remove(path)
        seen.add(path)
        ordered.append(path)

    for path in paths:
        visit(path)
    return ordered


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--lake", default="lake", help="Path to the Lake executable")
    args = parser.parse_args()
    paths, roots = validate_sources()
    ordered = dependency_order(paths)
    assert set(ordered) == project_dependencies(paths)
    protected = set(ordered) | {
        Path(__file__).resolve(), ROOT / "tools/verify_blind_upper_components.py",
        ROOT / "tools/verify_tier6.py", ROOT / "tools/entropy_tail_quantile_specification_freeze.json",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/entropy-tail-quantile" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    status = dict(valid=False, scope=SCOPE, source_sha256=hashes, exact_targets=EXACT_TARGETS,
                  exact_targets_checked=0, quantile_split_verified=False,
                  quantile_comparison_verified=False, entropy_tail_upper_verified=False,
                  entropy_tail_lower_verified=False, closed_quantile_minimax_verified=False,
                  commands=[])

    def save() -> None:
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    save()
    audit = LEAN / ".audit/EntropyTailQuantile.lean"
    audit.parent.mkdir(exist_ok=True)
    audit.write_text("".join("import " + PREFIX + m + "\n" for m in MODULES) + "\n" +
                     "".join(f"example : {t} := {d}\n" for d, t in EXACT_TARGETS.items()) + "\n" +
                     "".join("#print axioms " + r + "\n" for r in sorted(roots)), encoding="utf-8")
    commands = []
    for path in ordered:
        relative = path.relative_to(LEAN)
        olean = LEAN / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        commands.append([args.lake, "env", "lean", "-j", "1", "-o", str(olean.relative_to(LEAN)), str(relative)])
    commands.append([args.lake, "env", "lean", "-j", "1", str(audit.relative_to(LEAN))])
    for i, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        report = result.stdout + result.stderr
        (output / f"{i+1:03d}.log").write_text(report, encoding="utf-8")
        status["commands"].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f"{i+1}/{len(commands)} {command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(report, flush=True)
            return result.returncode
    status["axioms"] = validate_reports(report, result.returncode, roots)
    validate_sources()
    if any(sha(ROOT / p) != h for p, h in hashes.items()):
        raise ValueError("Protected source changed during audit")
    status.update(valid=True, audited_modules=len(paths), rebuilt_local_modules=len(ordered),
                  audited_declarations=len(roots), exact_targets_checked=len(EXACT_TARGETS),
                  quantile_split_verified=True, quantile_comparison_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
