"""Audit stopping-program and cap-identification ingredients, not full targets.

The default rebuilds the local closure. --cached-dependencies rebuilds only
the two ingredient groups and records the narrower checkpoint scope.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import DECLARATION, FORBIDDEN, sha, strip_comments, validate_reports
from verify_entropy_tail_components import dependency_order

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
GROUPS = {"StoppingProgram", "CapIdentification"}
EXACT = r"""
open MeasureTheory
open scoped BigOperators ENNReal
open ThresholdHC.StoppingProgram ThresholdHC.CapIdentification
example : ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d : ℕ),
    (∀ a : StopTree d × StopTree d,
      rootInformation r d a-κ*rootWork w d a ≤ rootBellman r w κ d) ∧
    ∃ a : StopTree d × StopTree d,
      rootInformation r d a-κ*rootWork w d a = rootBellman r w κ d := rootBellman_maximum
example : ∀ (r w : ℕ → ℕ → ℝ), (∀ n k, 0 ≤ w n k) → ∀ d κ,
    rootBellman r w κ d = 0 ↔ κ = ratioValue (rootInformation r d) (rootWork w d) := rootBellman_zero_iff
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → intensity f = 0 → ∀ s : CountState N,
    f.stopWeight s = 0 ∧ f.continueWeight s = 0 ∧ f.outputWeight s = 0 := flow_zero_intensity
example : ∀ {m : ℕ} (d : Fin m → ℝ) (N : ℕ), (∀ i, 0 < d i) → Function.Injective d → 0 < m →
    ((∀ g : Fin m → ℝ,
      (∀ j : Fin ((N+1)/2), (∑ i, g i*(d i)^(2*j.val+1)) = 0) → (∑ i, g i) = 0) ↔
        2*m-1 ≤ N) := moments_cap_threshold
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsFiniteMeasure μ]
    (qH qL : ThresholdHC.Tier6.SignLaw) (N : ℕ),
    (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) ↔
      ∀ s : CountState N, countCoefficient μ qH s = countCoefficient μ qL s :=
  odd_moments_iff_count_match
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    informationRatio μ N Q = 0 ↔
      ∀ j : Fin ((N+1)/2), ∫ d, (Q.high.val d-Q.low.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0 :=
  informationRatio_zero_iff_moments
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (N : ℕ) (S : Finset ThresholdHC.Tier6.Gap),
    μ.support = (S:Set ThresholdHC.Tier6.Gap) → 0 < S.card →
    ((∀ qH qL : ThresholdHC.Tier6.SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ qH → ThresholdHC.RareAboveTwo.RarePrior μ ρ qL →
      (∀ s : CountState N, countCoefficient μ qH s = countCoefficient μ qL s) →
      ThresholdHC.Tier6.signMean μ qH.val = ThresholdHC.Tier6.signMean μ qL.val) ↔
      2*S.card-1 ≤ N) := finite_support_target_threshold
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ],
    μ.support.Infinite → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ N : ℕ,
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ B : ℝ, c ≤ programSquared μ ρ B N := infinite_support_program_floor
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (qH qL : ThresholdHC.Tier6.SignLaw) (N : ℕ),
    (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) →
    ∀ (A : ThresholdHC.CriticalEntropy.StoppedProcedure R E), (∀ z, A.stop z ≤ N) →
    ThresholdHC.CriticalEntropy.cappedTranscriptLaw μ ν
      (ThresholdHC.ObservableSimulation.gapParameter false) (ThresholdHC.ObservableSimulation.gapParameter true)
      (ThresholdHC.ObservableSimulation.signUnit qH) A N =
    ThresholdHC.CriticalEntropy.cappedTranscriptLaw μ ν
      (ThresholdHC.ObservableSimulation.gapParameter false) (ThresholdHC.ObservableSimulation.gapParameter true)
      (ThresholdHC.ObservableSimulation.signUnit qL) A N := stopped_law_eq_of_odd_moments
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--cached-dependencies", action="store_true")
    args = parser.parse_args()
    paths = [p for g in sorted(GROUPS) for p in sorted((LEAN / "ThresholdHC" / g).glob("*.lean"))]
    roots = set()
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape: " + str(path))
        for name in DECLARATION.findall(source):
            root = "ThresholdHC." + path.parent.name + "." + name
            if root in roots:
                raise ValueError("Duplicate root: " + root)
            roots.add(root)
    ordered = dependency_order(paths)
    rebuilt = [p for p in ordered if p.parent.name in GROUPS] if args.cached_dependencies else ordered
    protected = set(ordered) | {Path(__file__).resolve(), ROOT / "tools/verify_blind_upper_components.py",
        ROOT / "tools/verify_entropy_tail_components.py", ROOT / "tools/verify_tier6.py",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml"}
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/stopping-components" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/StoppingComponents.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Bellman, price-ratio, perspective, flow bounds, exact count/stopped-law moment equivalence, support target thresholds and the primal bias-floor lower direction.",
        full_stopping_program_verified=False, four_prior_duality_verified=False,
        full_cap_identification_verified=False, full_genie_convergence_verified=False,
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
        commands.append([args.lake,"env","lean","-j","1","-o",str(obj),str(rel)])
    commands.append([args.lake,"env","lean","-j","1",str(audit.relative_to(LEAN))])
    for n, command in enumerate(commands, 1):
        result = subprocess.run(command,cwd=LEAN,capture_output=True,text=True,encoding="utf-8")
        report = result.stdout+result.stderr
        (output / f"{n:03d}.log").write_text(report,encoding="utf-8")
        status["commands"].append(dict(command=command,exit_code=result.returncode))
        save()
        print(f"{n}/{len(commands)} {command[-1]}: exit {result.returncode}",flush=True)
        if result.returncode:
            print(report,flush=True)
            return result.returncode
    status["axioms"] = validate_reports(report,result.returncode,roots)
    if any(sha(ROOT / p) != h for p,h in hashes.items()) or sha(audit) != audit_hash:
        raise ValueError("Source changed during audit")
    status.update(valid=True,exact_types_checked=9,
        count_law_equivalence_verified=True, stopped_law_equivalence_verified=True,
        support_target_threshold_verified=True, zero_information_characterization_verified=True)
    save()
    print(json.dumps(dict(valid=True,modules=len(paths),declarations=len(roots),evidence=str(output))),flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
