"""Audit the reference-prior absorption and factor-three midpoint comparison.

Default: rebuild every local dependency. --cached-dependencies: rebuild the
five reference-absorption modules and record all other dependency source hashes.
Neither mode claims the factor-sixteen risk comparison or genie convergence.
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
MAINS = [LEAN / "ThresholdHC/StoppingProgram/MidpointComparison.lean"]
NEW_MODULES = {"PriorMixtures", "PerspectiveMonotonic", "AbsorbedPriors", "AbsorptionRatio", "MidpointComparison"}
REQUIRED = {"ThresholdHC.StoppingProgram." + name for name in (
    "midpoint_comparison", "absorbedPriors_informationRatio_le", "absorbedPriors_admissible",
    "absorbedPriors_gap", "absorbedPriors_perspective_le", "dualValue_le_nine_midpointSquared")}
EXACT = r"""
open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    midpointValue μ ρ B N ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤ 3*midpointValue μ ρ B N := midpoint_comparison
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N →
    (⨆ (q : SignLaw) (r : SignLaw) (_ : RarePrior μ ρ q) (_ : RarePrior μ ρ r),
      dualRatio μ B N (midpointFourPriors q r)) ^ (1/(2:ℝ)) ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 3*(⨆ (q : SignLaw) (r : SignLaw)
      (_ : RarePrior μ ρ q) (_ : RarePrior μ ρ r),
      dualRatio μ B N (midpointFourPriors q r)) ^ (1/(2:ℝ)) := by
  intro μ inst ρ B N hρ hρquarter hB _hN
  exact midpoint_comparison μ ρ B N hρ (by linarith) hB
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    informationRatio μ N (absorbedPriors Q) ≤ informationRatio μ N Q :=
  absorbedPriors_informationRatio_le
"""


def validate_sources():
    ordered = dependency_order(MAINS)
    paths = [p for p in ordered if p.parent.name == "StoppingProgram"]
    roots = set()
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape: " + str(path))
        for name in DECLARATION.findall(source):
            root = "ThresholdHC.StoppingProgram." + name
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
    output = args.output_dir or ROOT / ".runtime/reference-absorption" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/ReferenceAbsorption.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Reference absorption preserves global rarity, scales the target gap by one third, and decreases the information/work ratio; the actual stopping-program value lies between the two-prior midpoint modulus and three times that modulus.",
        full_stopping_program_verified=False, reference_absorption_verified=False,
        midpoint_comparison_verified=False, finite_risk_certificate_verified=False,
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
    status.update(valid=True, exact_types_checked=3, reference_absorption_verified=True,
        midpoint_comparison_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
