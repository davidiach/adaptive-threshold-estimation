"""Audit the full observable entropy-tail and closed-quantile upper theorems.

By default every local dependency is rebuilt. The explicit checkpoint option
uses cached dependencies outside the sampling/execution construction and records
that narrower scope. Frozen model/specification files are checked in both modes.
The statistical lower bound and stopping-program theorems are not certified.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import DECLARATION, FORBIDDEN, sha, strip_comments, validate_reports
from verify_entropy_tail_components import dependency_order, validate_sources as validate_frozen

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
GROUPS = ("EntropyTailQuantile", "EntropyTailUpper", "EntropyTailAssembly", "EntropyTailSampling", "EntropyTailExecution")
NEW_GROUPS = {"EntropyTailSampling", "EntropyTailExecution"}
TARGETS = {
    "ThresholdHC.EntropyTailQuantile.quantile_split": "ThresholdHC.EntropyTailQuantile.QuantileSplitStatement",
    "ThresholdHC.EntropyTailQuantile.quantile_comparison": "ThresholdHC.EntropyTailQuantile.QuantileComparisonStatement",
    "ThresholdHC.EntropyTailExecution.entropy_tail_upper": "ThresholdHC.EntropyTailQuantile.EntropyTailUpperStatement",
    "ThresholdHC.EntropyTailExecution.closed_quantile_upper": "ThresholdHC.EntropyTailQuantile.ClosedQuantileUpperStatement",
}
EXACT_CHECKS = r"""
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 28000*selectionValue μ ρ B :=
  fun μ _ _ _ => ThresholdHC.EntropyTailExecution.entropy_tail_upper_28000 μ
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 30001*closedQuantileValue μ ρ B :=
  fun μ _ _ _ => ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001 μ
"""


def validate_sources() -> tuple[list[Path], set[str]]:
    validate_frozen()
    paths = [p for group in GROUPS for p in sorted((LEAN / "ThresholdHC" / group).glob("*.lean"))]
    if any(not any(p.parent.name == group for p in paths) for group in GROUPS):
        raise ValueError("Missing construction module group")
    roots: set[str] = set()
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        for name in DECLARATION.findall(source):
            root = "ThresholdHC." + path.parent.name + "." + name
            if root in roots:
                raise ValueError("Duplicate declaration: " + root)
            roots.add(root)
    if not set(TARGETS) <= roots or not {
        "ThresholdHC.EntropyTailExecution.entropy_tail_upper_28000",
        "ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001",
    } <= roots:
        raise ValueError("Missing exact target")
    return paths, roots


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--cached-dependencies", action="store_true")
    args = parser.parse_args()
    paths, roots = validate_sources()
    ordered = dependency_order(paths)
    rebuilt = [p for p in ordered if p.parent.name in NEW_GROUPS] if args.cached_dependencies else ordered
    protected = set(ordered) | {
        Path(__file__).resolve(), ROOT / "tools/verify_entropy_tail_components.py",
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_tier6.py",
        ROOT / "tools/entropy_tail_quantile_specification_freeze.json", LEAN / "lean-toolchain",
        LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/entropy-tail-upper" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    status = dict(
        valid=False, scope="Observable arbitrary-law entropy-tail upper and closed-quantile upper; deterministic quantile comparison.",
        entropy_tail_upper_verified=False, closed_quantile_upper_verified=False,
        entropy_tail_lower_verified=False, closed_quantile_minimax_verified=False,
        stopping_program_verified=False, marked_poisson_realization_verified=False,
        local_dependency_rebuild_performed=not args.cached_dependencies,
        module_count=len(paths), declaration_count=len(roots), source_sha256=hashes,
        roots=sorted(roots), exact_types_checked=0, rebuilt_local_modules=len(rebuilt), commands=[],
    )

    def save() -> None:
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    save()
    audit = LEAN / ".audit/EntropyTailUpper.lean"
    audit.parent.mkdir(exist_ok=True)
    audit_text = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    audit_text += "".join(f"example : {target} := {root}\n" for root, target in TARGETS.items())
    audit_text += EXACT_CHECKS + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(audit_text)):
        raise ValueError("Forbidden audit source")
    audit.write_text(audit_text, encoding="utf-8")
    status["audit_source_sha256"] = sha(audit)
    commands = []
    for path in rebuilt:
        relative = path.relative_to(LEAN)
        olean = Path(".lake/build/lib/lean") / relative.with_suffix(".olean")
        (LEAN / olean).parent.mkdir(parents=True, exist_ok=True)
        commands.append([args.lake, "env", "lean", "-j", "1", "-o", str(olean), str(relative)])
    commands.append([args.lake, "env", "lean", "-j", "1", str(audit.relative_to(LEAN))])
    for index, command in enumerate(commands, 1):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        report = result.stdout + result.stderr
        (output / f"{index:03d}.log").write_text(report, encoding="utf-8")
        status["commands"].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f"{index}/{len(commands)} {command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(report, flush=True)
            return result.returncode
    status["axioms"] = validate_reports(report, result.returncode, roots)
    validate_sources()
    if any(sha(ROOT / path) != digest for path, digest in hashes.items()):
        raise ValueError("Protected source changed during audit")
    if sha(audit) != status["audit_source_sha256"]:
        raise ValueError("Audit source changed during checking")
    status.update(valid=True, exact_types_checked=len(TARGETS)+2,
                  entropy_tail_upper_verified=True, closed_quantile_upper_verified=True,
                  marked_poisson_realization_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
