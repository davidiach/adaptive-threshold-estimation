"""Audit the exact robust and finite-law stopping-program reductions.

Default: rebuild every local dependency. --cached-dependencies: rebuild the
two constraint-reduction modules and record all other dependency source hashes.
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
MAIN = LEAN / "ThresholdHC/StoppingProgram/FiniteProgram.lean"
NEW_MODULES = {"RobustRarity", "FiniteProgram"}
REQUIRED = {"ThresholdHC.StoppingProgram." + name for name in (
    "feasible_iff_finite_program", "finiteTailBound_iff", "finite_law_integral", "feasible_iff_four_cutoffs",
    "robust_polynomial_bound_iff", "fractional_rarity_support_explicit")}
EXACT = r"""
open MeasureTheory Polynomial
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {I : Type} [Fintype I] (μ : Measure Gap) (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 ≤ w i) → (μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) →
    ∀ (ρ : ℝ) (P : ℝ[X]) (z : ℝ),
    (∃ (ell : ℝ) (u : I → ℝ), 0 ≤ ell ∧ (∀ i, 0 ≤ u i ∧ P.eval (d i:ℝ)-ell ≤ u i) ∧
      ρ*ell+∑ i, w i*u i ≤ z) ↔
    ∃ ell, 0 ≤ ell ∧ ρ*ell+(∫ x : Gap, max (P.eval (x:ℝ)-ell) 0 ∂μ) ≤ z :=
  by
    intro I inst μ w d hw hμ ρ P z
    exact finiteTailBound_iff μ w d hw hμ ρ P z
example : ∀ {I : Type} [Fintype I] {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap), (∀ i, 0 ≤ w i) →
    (μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) →
    ∀ ρ B, 0 < ρ → ∀ C : Certificate N,
    Feasible μ ρ B C ↔ FlowCone C.flow ∧ 0 ≤ C.bias ∧ 0 ≤ C.variance ∧
      FiniteTailBound w d ρ (biasPolynomial C)
        (C.bias-(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (-biasPolynomial C)
        (C.bias+(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.momentWeight)
        (C.variance-finiteNullMean w d C.flow.momentWeight) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.continueWeight)
        (B-finiteNullMean w d C.flow.continueWeight) :=
  by
    intro I inst N μ prob w d hw hμ ρ B hρ C
    exact feasible_iff_finite_program μ w d hw hμ hρ C
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
    output = args.output_dir or ROOT / ".runtime/finite-stopping-program" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/FiniteStoppingProgram.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Exact equivalence of robust certificate feasibility with a finite system of cone, cutoff and linear excess inequalities for every finitely supported law.",
        full_stopping_program_verified=False, finite_program_equivalence_verified=False,
        robust_cutoff_reduction_verified=False,
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
    status.update(valid=True, exact_types_checked=2, finite_program_equivalence_verified=True,
        robust_cutoff_reduction_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
