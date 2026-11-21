"""Audit two auxiliary results of the v6 appendix on localized rare-event scales.

Theorem loc:thm:counter of paper/v6/appendix-localization.tex shows that the
proposed rescaling heuristic H(h) = rho omega(h/sqrt rho) fails: at
mu = rho delta_(rho^2) + (1-rho) delta_(1/4) and B = rho^-4 the rare minimax
RMS risk is of order rho while H = O(rho^2), so H can underestimate it by an
unbounded factor. Proposition loc:prop:noise shows why the original
unmodified variance is not rarity-scaled: at one fixed negative coin of gap
d < 1/2 the level-0 term of the geometric single-term estimator forces the
second moment (1/2-d)/(1-2^-1/2). The group checks the counterexample with
rho/100 <= R <= rho/2 and H <= 3 rho^2, the unbounded factor, the noise floor
in variance form for the 713-threshold estimator, as a second-moment floor
for the original untruncated estimator, and in truncated form in the frozen
finite model.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the six targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written before the proofs
and reviewed before the pin; they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "LocalizationCounter"
NAMES = ("Specification", "Information", "CounterLaw", "Counter", "Noise", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "8468442bf0e61bf26c2f2a6247b61dfd91fa1ebf2fe366b282688c0d36d14731"
TARGETS = {
    "LocalizationCounter.counter_law_probability": "LocalizationCounter.CounterLawProbabilityStatement",
    "LocalizationCounter.counterexample": "LocalizationCounter.CounterexampleStatement",
    "LocalizationCounter.counter_unbounded": "LocalizationCounter.CounterUnboundedStatement",
    "LocalizationCounter.observable713_noise_floor": "LocalizationCounter.Observable713NoiseFloorStatement",
    "LocalizationCounter.original_second_moment_floor": "LocalizationCounter.OriginalSecondMomentFloorStatement",
    "LocalizationCounter.truncated_noise_floor": "LocalizationCounter.TruncatedNoiseFloorStatement",
}
COMPONENTS = (
    "LocalizationCounter.counter_minimax_lower",
    "LocalizationCounter.counter_minimax_upper",
    "LocalizationCounter.counter_heuristic_eq",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (ρ : ℝ) (d : Gap), 0 ≤ ρ → ρ ≤ 1 → IsProbabilityMeasure (counterLaw ρ d) :=
  LocalizationCounter.counter_law_probability

example :
  ∀ (ρ : ℝ) (d : Gap), 0 < ρ → ρ ≤ 1/4 → (d : ℝ) = ρ^2 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ = counterLaw ρ d →
      ENNReal.ofReal (ρ/100) ≤ rareMinimaxRisk μ ρ (1/ρ^4) ∧
      rareMinimaxRisk μ ρ (1/ρ^4) ≤ ENNReal.ofReal (ρ/2) ∧
      heuristic μ ρ (1 / Real.sqrt (1/ρ^4)) = ρ^2 + 4*(1-ρ)*ρ^2*Real.sqrt ρ ∧
      heuristic μ ρ (1 / Real.sqrt (1/ρ^4)) ≤ 3*ρ^2 :=
  LocalizationCounter.counterexample

example :
  ∀ K : ℝ, 0 < K → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (ρ : ℝ) (d : Gap), 0 < ρ → ρ ≤ ρ₀ → ρ ≤ 1/4 → (d : ℝ) = ρ^2 →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ = counterLaw ρ d →
        ENNReal.ofReal (K * heuristic μ ρ (1 / Real.sqrt (1/ρ^4))) <
          rareMinimaxRisk μ ρ (1/ρ^4) :=
  LocalizationCounter.counter_unbounded

example :
  ∀ d : Gap, (d : ℝ) < 1/2 →
    MemLp (populationOutput Observable713.observableEstimator) 2
        (experimentLaw (Measure.dirac d) Observable713.observableEstimator negativeSign) ∧
    (∫ z, populationOutput Observable713.observableEstimator z
        ∂experimentLaw (Measure.dirac d) Observable713.observableEstimator negativeSign) = 0 ∧
    ENNReal.ofReal ((1/2 - (d : ℝ)) / (1 - rLevel)) ≤
      evariance (populationOutput Observable713.observableEstimator)
        (experimentLaw (Measure.dirac d) Observable713.observableEstimator negativeSign) ∧
    0 < (1/2 - (d : ℝ)) / (1 - rLevel) :=
  LocalizationCounter.observable713_noise_floor

example :
  ∀ d : Gap, (d : ℝ) < 1/2 →
    ENNReal.ofReal ((1/2 - (d : ℝ)) / (1 - rLevel)) ≤
      ∫⁻ x, ENNReal.ofReal ((Uniform713.estimator
          (fun j ω => Tier2.Model.decision
            (fun k => Uniform713.dyadicMean Tier2.observations k ω) j) x) ^ 2)
        ∂Uniform713.samplingMeasure
          (Tier2.tapeMeasure (ObservableSimulation.gapParameter false d)) :=
  LocalizationCounter.original_second_moment_floor

example :
  ∀ (L : ℕ) (d : ℝ), 0 < d → d < 1/2 →
    (1/2 - d) / (1 - rLevel) ≤ secondMomentK 1 1 L d false ∧
    (1/2 - d) / (1 - rLevel) -
        (∑ x : Fin (2^L) → Bool, streamProb (coinP d false) x * zK 1 1 L x)^2 ≤
      secondMomentK 1 1 L d false -
        (∑ l ∈ Finset.range (L+1), ∑ x : Fin (2^L) → Bool,
          streamProb (coinP d false) x * deltaK 1 1 l x)^2 :=
  LocalizationCounter.truncated_noise_floor

example : ∀ (ρ : ℝ) (d : Gap), 0 < ρ → ρ ≤ 1/4 → (d : ℝ) = ρ^2 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ = counterLaw ρ d →
    ENNReal.ofReal (ρ/40) ≤ rareMinimaxRisk μ ρ (1/ρ^4) :=
  LocalizationCounter.counter_minimax_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ →
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (ρ/2) :=
  LocalizationCounter.counter_minimax_upper

example : ∀ (ρ : ℝ) (d : Gap), 0 < ρ → ρ ≤ 1/4 → (d : ℝ) = ρ^2 →
    heuristic (counterLaw ρ d) ρ (1 / Real.sqrt (1/ρ^4)) =
      ρ^2 + 4*(1-ρ)*ρ^2*Real.sqrt ρ :=
  LocalizationCounter.counter_heuristic_eq
"""


def modules() -> list[str]:
    return [f"{GROUP}.{name}" for name in NAMES]


def declared_roots() -> set[str]:
    found = {p.stem for p in SOURCE.glob("*.lean")}
    if found != set(NAMES) or len(NAMES) != len(set(NAMES)):
        raise ValueError(f"Unregistered or missing {GROUP} module")
    roots: list[str] = []
    for name in NAMES:
        source = strip_comments((SOURCE / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in {GROUP}/{name}.lean")
        names_here = public_names(source, f"{GROUP}/{name}.lean")
        if any(not root.startswith(f"ThresholdHC.{GROUP}.") for root in names_here):
            raise ValueError(f"{GROUP}/{name}.lean must declare in ThresholdHC.{GROUP}")
        roots.extend(names_here)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate localization-counter declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing localization-counter target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed localization-counter specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.LocalizationCounter",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?{re.escape(name)}\n", EXACT)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return ["ThresholdHC." + module for module in modules()]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--replay", action="store_true",
                        help="also replay the registered modules through leanchecker")
    parser.add_argument("--jobs", type=int, default=3, help="parallel kernel replays")
    args = parser.parse_args()
    source, roots = audit_input()
    subprocess.run(["lake", "build", *replay_modules()], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    if args.replay:
        from verify_project_axioms import replay
        replay(replay_modules(), "lake", args.jobs)
        print(f"Replayed {len(modules())} modules through the independent kernel checker")
    print(f"All {len(TARGETS)} localization-counter targets are certified")


if __name__ == "__main__":
    main()
