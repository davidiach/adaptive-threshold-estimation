"""Audit exact infinite-cap duality, attainment and minimax comparisons.

Default: rebuild every local dependency. --cached-dependencies rebuilds the
fourteen infinite-cap modules and records the other dependency source hashes.
Neither mode claims latent-reveal convergence or the entropy-tail lower bound.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

from verify_blind_upper_components import DECLARATION, FORBIDDEN, sha, strip_comments, validate_reports
from verify_entropy_tail_components import dependency_order

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
MAINS = [LEAN / "ThresholdHC/Genie/InfiniteMidpoint.lean", LEAN / "ThresholdHC/Genie/CapLimits.lean"]
NEW_MODULES = {"Model", "FlowExtension", "CapMonotonicity", "CapLimits", "InfiniteComparison",
    "InfiniteCoordinates", "PerspectiveTopology", "InformationTopology", "DualTopology",
    "CompactDecreasingMaximum", "CompactPriorDomain", "InfiniteDualLimit", "InfiniteDuality", "InfiniteMidpoint"}
REQUIRED = {"ThresholdHC.Genie." + name for name in (
    "infinite_four_prior_duality", "infinite_dual_positive_attained", "infinite_midpoint_comparison",
    "infinite_program_comparison", "informationRatio_mono", "programValue_antitone",
    "programValue_tendsto", "informationRatio_tendsto", "lowerSemicontinuous_perspective",
    "compact_decreasing_maximum")}

EXACT = r"""
open MeasureTheory Filter
open scoped ENNReal Topology
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∀ {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    infiniteProgramValue μ ρ B ^ 2 = infiniteDualValue μ ρ B ∧
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 := infinite_four_prior_duality
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∀ {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 ∧
      0 < infiniteProgramValue μ ρ B ^ 2 ∧ infiniteInformationRatio μ Q < ⊤ := infinite_dual_positive_attained
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    infiniteMidpointValue μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ 3*infiniteMidpointValue μ ρ B := infinite_midpoint_comparison
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ 8*rareMinimaxRisk μ ρ B := infinite_program_comparison
example : ∀ (μ : Measure Gap) (Q : FourPriors),
    Monotone (fun N => informationRatio μ N Q) := informationRatio_mono
example : ∀ (μ : Measure Gap) (ρ B : ℝ),
    Antitone (fun N => programValue μ ρ B N) := programValue_antitone
example : ∀ (μ : Measure Gap) (ρ B : ℝ),
    Tendsto (fun N : ℕ => programValue μ ρ B (N+1)) atTop
      (𝓝 (infiniteProgramValue μ ρ B)) := programValue_tendsto
example : ∀ (μ : Measure Gap) (Q : FourPriors),
    Tendsto (fun N : ℕ => informationRatio μ (N+1) Q) atTop
      (𝓝 (infiniteInformationRatio μ Q)) := informationRatio_tendsto
"""


def validate_sources():
    ordered = dependency_order(MAINS)
    paths = [p for p in ordered if p.parent.name == "Genie"]
    roots = set()
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape: " + str(path))
        for name in DECLARATION.findall(source):
            root = "ThresholdHC.Genie." + name
            if root in roots:
                raise ValueError("Duplicate root: " + root)
            roots.add(root)
    if REQUIRED - roots:
        raise ValueError("Missing exact target or required dependency: " + ", ".join(sorted(REQUIRED - roots)))
    if FORBIDDEN.search(strip_comments(EXACT)):
        raise ValueError("Forbidden exact audit source")
    return ordered, paths, roots


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--cached-dependencies", action="store_true")
    args = parser.parse_args()
    ordered, paths, roots = validate_sources()
    rebuilt = [p for p in paths if p.stem in NEW_MODULES] if args.cached_dependencies else ordered
    protected = set(ordered) | {Path(__file__).resolve(), ROOT / "tools/verify_blind_upper_components.py",
        ROOT / "tools/verify_entropy_tail_components.py", ROOT / "tools/verify_tier6.py",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml"}
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/infinite-cap-dual" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/InfiniteCapDual.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Exact attained infinite-cap four-prior dual, factor-three midpoint and factor-eight original minimax comparisons, with monotone cap limits. No latent-reveal convergence or entropy-tail statistical lower bound is claimed.",
        infinite_cap_duality_verified=False, infinite_cap_comparisons_verified=False,
        full_genie_convergence_verified=False, entropy_tail_lower_verified=False,
        local_dependency_rebuild_performed=not args.cached_dependencies,
        module_count=len(paths), declaration_count=len(roots), exact_types_checked=0,
        rebuilt_local_modules=len(rebuilt), source_sha256=hashes, roots=sorted(roots), commands=[],
        audit_source_sha256=audit_hash)

    def save():
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    save()
    commands = []
    for path in rebuilt:
        rel = path.relative_to(LEAN)
        obj = Path(".lake/build/lib/lean") / rel.with_suffix(".olean")
        (LEAN / obj).parent.mkdir(parents=True, exist_ok=True)
        commands.append([args.lake, "env", "lean", "-j", "1", "-o", str(obj), str(rel)])
    commands.append([args.lake, "env", "lean", "-j", "1", str(audit.relative_to(LEAN))])
    for n, command in enumerate(commands, 1):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        report = result.stdout + result.stderr
        (output / f"{n:03d}.log").write_text(report, encoding="utf-8")
        status["commands"].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f"{n}/{len(commands)} {command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(report, flush=True)
            return result.returncode
    status["axioms"] = validate_reports(report, result.returncode, roots)
    if any(sha(ROOT / p) != h for p, h in hashes.items()) or sha(audit) != audit_hash:
        raise ValueError("Source changed during audit")
    status.update(valid=True, exact_types_checked=8, infinite_cap_duality_verified=True, infinite_cap_comparisons_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
