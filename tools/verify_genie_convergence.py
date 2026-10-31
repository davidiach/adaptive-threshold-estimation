"""Audit actual posterior information, vanishing reveal error and optimized brackets.

Default rebuilds every local dependency. --cached-dependencies rebuilds the
twelve new posterior/convergence modules and hashes all other dependencies.
The entropy-tail statistical lower bound is outside this audit.
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
MAINS = [LEAN / "ThresholdHC/Genie/OptimizedConvergence.lean"]
NEW_MODULES = {"ReferenceRegularization", "OptimizedBrackets", "TapeIdentification", "LatentModel",
    "LatentScore", "ObservationFiltration", "LatentTape", "FinitePosterior", "LatentMoments",
    "LatentPrefix", "RevealConvergence", "OptimizedConvergence"}
REQUIRED = {"ThresholdHC.Genie." + name for name in (
    "latentScore_secondMoment", "posterior_secondMoment_eq_terminal", "latent_score_posterior_tendsto",
    "terminalInformation_tendsto", "revealResidual_tendsto_zero", "genieInformationRatio_tendsto",
    "regularized_latentDivergence_bound", "regularized_infiniteInformation", "genieSquared_sup_eq_infinite",
    "genieValue_tendsto", "genie_risk_bracket", "genie_stopping_terminates")}

EXACT = r"""
open MeasureTheory Filter
open scoped ENNReal Topology
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    (∫⁻ z, ENNReal.ofReal ((latentScore Q z)^2) ∂latentReference μ Q.variance) = latentDivergence μ Q :=
  latentScore_secondMoment
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    ∀ n : ℕ, (∫⁻ z, ENNReal.ofReal ((((latentTapeLaw μ Q.variance)[latentTapeScore Q |
      observationFiltration latentObservedTape measurable_latentObservedTape n]) z)^2)
        ∂latentTapeLaw μ Q.variance) = terminalInformation μ Q n := posterior_secondMoment_eq_terminal
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    let P := latentTapeLaw μ Q.variance
    let ℱ := observationFiltration latentObservedTape measurable_latentObservedTape
    ∀ᵐ z ∂P, Tendsto (fun n => (P[latentTapeScore Q | ℱ n]) z) atTop (𝓝 (latentTapeScore Q z)) :=
  latent_score_posterior_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (terminalInformation μ Q) atTop (𝓝 (latentDivergence μ Q)) := terminalInformation_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (revealResidual μ Q) atTop (𝓝 0) := revealResidual_tendsto_zero
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (fun n : ℕ => genieInformationRatio μ (n+1) Q) atTop (𝓝 (infiniteInformationRatio μ Q)) :=
  genieInformationRatio_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1), 0 < ε →
    latentDivergence μ (regularizedPriors Q ε hε) ≤ ENNReal.ofReal (4/ε) := regularized_latentDivergence_bound
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1), ε < 1 → infiniteInformationRatio μ (regularizedPriors Q ε hε) ≤
      ENNReal.ofReal (1/(1-ε))*infiniteInformationRatio μ Q := regularized_infiniteInformation
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    (⨆ n : ℕ, genieSquared μ ρ B (n+1)) = infiniteProgramValue μ ρ B ^ 2 := genieSquared_sup_eq_infinite
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    Tendsto (fun n : ℕ => genieValue μ ρ B (n+1)) atTop (𝓝 (infiniteProgramValue μ ρ B)) := genieValue_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 < ρ → ρ ≤ 1/2 → 0 < B →
    ∀ N : ℕ, 0 < N → genieValue μ ρ B N/8 ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N := genie_risk_bracket
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    ∃ N : ℕ, 0 < N ∧ programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧ programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B :=
  genie_stopping_terminates
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
    output = args.output_dir or ROOT / ".runtime/genie-convergence" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/GenieConvergence.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Actual latent posterior moments, finite-divergence residual convergence, optimized genie convergence, risk brackets and finite termination. Entropy-tail statistical lower bound, finite-support genie SOCP and infinite-divergence counterexample are outside this audit.",
        posterior_information_verified=False, residual_convergence_verified=False,
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
    status.update(valid=True, exact_types_checked=12, posterior_information_verified=True, residual_convergence_verified=True, full_genie_convergence_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
