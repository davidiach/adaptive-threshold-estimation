"""Audit sharp affinity testing, adaptive population transfer and prior contraction.

Default: rebuild every local dependency. --cached-dependencies: rebuild the
nine adaptive-testing modules and record all other dependency source hashes.
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
MAINS = [LEAN / "ThresholdHC/StoppingProgram/PrefixModulus.lean"]
NEW_MODULES = {"AffinityOverlap", "AffinityRisk", "FinitePopulationInformation",
    "CreationInformation", "ObservableInformation", "PriorContraction", "PrefixRisk",
    "ContractionScale", "PrefixModulus"}
REQUIRED = {"ThresholdHC.StoppingProgram." + name for name in (
    "affinity_squared_risk", "affinity_rms_risk", "finite_population_information",
    "creation_population_information", "observable_prefix_information_budget",
    "contractPrior_informationRatio", "observable_prefix_risk", "prefix_program_bound")}

EXACT = r"""
open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ {Ω : Type} [MeasurableSpace Ω],
    ∀ (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    ∀ (f : Ω → ℝ), Measurable f → ∀ a b : ℝ,
    ENNReal.ofReal ((b-a)^2*(hellingerAffinity P Q).toReal^2/4) ≤
      max (squaredRisk P f a) (squaredRisk Q f b) := affinity_squared_risk
example : ∀ {Ω : Type} [MeasurableSpace Ω],
    ∀ (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    ∀ (f : Ω → ℝ), Measurable f → ∀ a b : ℝ, a ≤ b →
    ENNReal.ofReal ((b-a)*(hellingerAffinity P Q).toReal/2) ≤
      max (rootMeanRisk P f a) (rootMeanRisk Q f b) := affinity_rms_risk
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (q r : SignLaw) (N : ℕ) (B : ℝ), 0 ≤ B →
    expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B →
    1-(hellingerAffinity
      ((experimentLaw μ A q).map (fun z => (z.1.1,processPrefix N z.2)))
      ((experimentLaw μ A r).map (fun z => (z.1.1,processPrefix N z.2)))).toReal ≤
      (informationRatio μ N (midpointFourPriors q r)).toReal/4*B := by
  intro R _ μ _ A q r N B hB hw
  simpa only [observablePrefixLaw] using observable_prefix_information_budget μ A q r N B hB hw
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    ∀ (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1),
    signMean μ (contractPrior r q s hs).val-signMean μ (contractPrior q r s hs).val =
      s*(signMean μ r.val-signMean μ q.val) := contractPrior_gap
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    ∀ (N : ℕ) (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1),
    informationRatio μ N (midpointFourPriors (contractPrior q r s hs) (contractPrior r q s hs)) =
      ENNReal.ofReal (s^2)*informationRatio μ N (midpointFourPriors q r) := contractPrior_informationRatio
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (q r : SignLaw) (N : ℕ) (B : ℝ), 0 ≤ B →
    expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B →
    signMean μ q.val ≤ signMean μ r.val →
    ∀ (f : R × (Fin N → Option Bool) → ℝ), Measurable f →
    ENNReal.ofReal ((signMean μ r.val-signMean μ q.val)/2 *
      (1-(informationRatio μ N (midpointFourPriors q r)).toReal*B/4)) ≤
        max (rootMeanRisk (observablePrefixLaw μ A q N) f (signMean μ q.val))
          (rootMeanRisk (observablePrefixLaw μ A r N) f (signMean μ r.val)) := observable_prefix_risk
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (ρ B : ℝ), 0 < ρ → ρ ≤ 1/2 → 0 < B → RareBudget μ A ρ B →
    ∀ (N : ℕ) (f : R × (Fin N → Option Bool) → ℝ), Measurable f →
    ∀ T : ℝ≥0∞, (∀ u : SignLaw, RarePrior μ ρ u →
      rootMeanRisk (observablePrefixLaw μ A u N) f (signMean μ u.val) ≤ T) →
    programValue μ ρ B N ≤ 8*T := prefix_program_bound
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
    output = args.output_dir or ROOT / ".runtime/adaptive-information" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/AdaptiveInformation.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Sharp affinity testing for arbitrary measurable estimators; midpoint information transfers to the actual adaptive population prefix experiment with exact K/4 work constant; symmetric prior contraction scales the actual ratio quadratically.",
        full_stopping_program_verified=False, adaptive_population_transfer_verified=False,
        sharp_affinity_testing_verified=False, finite_risk_certificate_verified=False,
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
    status.update(valid=True, exact_types_checked=7, adaptive_population_transfer_verified=True,
        sharp_affinity_testing_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
