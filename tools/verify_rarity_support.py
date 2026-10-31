"""Audit the rarity support formula with an explicit fractional cutoff optimizer.

Default: rebuild every local dependency. --cached-dependencies: rebuild the
six rarity-support modules and record all other dependency source hashes.
Neither mode claims statistical flow realization or the risk certificate.
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
MAIN = LEAN / "ThresholdHC/StoppingProgram/RarityTheorem.lean"
NEW_MODULES = {"FunctionMomentImage", "RarityMultiplier", "RaritySupport", "RarityOptimality", "FractionalCutoff", "RarityTheorem"}
REQUIRED = {"ThresholdHC.StoppingProgram." + name for name in (
    "fractional_rarity_support_explicit", "fractional_rarity_support_of_memLp", "rareFunctional_eq_sSup",
    "rarity_function_multiplier", "upper_tail_equality_cutoff", "fractional_cutoff_preserves")}
EXACT = r"""
open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
example : ∀ (μ : Measure Gap) (ρ : ℝ) (f : Gap → ℝ),
    rareFunctional μ ρ f = sSup {r : ℝ | ∃ q : SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ q ∧ r = ∫ d, q.val d*f d ∂μ} := rareFunctional_eq_sSup
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ M : ℝ), 0 < ρ → 0 ≤ M →
    ∀ f : Gap → ℝ, Measurable f → MemLp f 2 μ → (∀ᵐ d ∂μ, f d ≤ M) →
    ∃ (ell c : ℝ) (q : SignLaw), 0 ≤ ell ∧ ell ≤ M ∧ 0 ≤ c ∧ c ≤ 1 ∧
      (∀ d, q.val d = if ell < f d then 1 else if f d = ell then c else 0) ∧
      signMean μ q.val ≤ ρ ∧
      sSup {r : ℝ | ∃ p : SignLaw, signMean μ p.val ≤ ρ ∧ r = ∫ d, p.val d*f d ∂μ} =
        ∫ d, q.val d*f d ∂μ ∧
      (∫ d, q.val d*f d ∂μ) = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      (∀ t : ℝ, 0 ≤ t → ρ*ell+(∫ d, max (f d-ell) 0 ∂μ) ≤
        ρ*t+∫ d, max (f d-t) 0 ∂μ) ∧
      (0 < ell → signMean μ q.val = ρ) :=
  fun μ _ ρ M hρ hM f hf hLp hb => fractional_rarity_support_explicit μ hρ hM f hf hLp hb
"""


def validate_sources():
    ordered = dependency_order([MAIN])
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
    output = args.output_dir or ROOT / ".runtime/rarity-support" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/RaritySupport.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Rarity support: raw supremum, attained scalar minimum, explicit fractional cutoff optimizer, bounded cutoff and positive-cutoff saturation.",
        full_stopping_program_verified=False, rarity_support_formula_verified=False,
        fractional_cutoff_optimizer_verified=False,
        statistical_flow_realization_verified=False, finite_risk_certificate_verified=False,
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
    status.update(valid=True, exact_types_checked=2, rarity_support_formula_verified=True,
        fractional_cutoff_optimizer_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
