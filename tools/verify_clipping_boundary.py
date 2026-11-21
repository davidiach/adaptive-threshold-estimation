"""Audit the clipping boundary of the nonlinear-population audit note.

The note CLIPPING_BOUNDARY.tex of the nonlinear-population package proves that
clipping to [0, rho] transfers a variance lower bound to the clipped squared
risk under bounded kurtosis, E(clip F - theta)^2 >= min(sigma^2, rho^2) /
(256 K^2), with a uniform corollary for the clipped estimator, and that no
unrestricted variance transfer holds: independent seed noise leaves F
unbiased, adds eps M^2 to its variance and at most eps rho^2 to the clipped
squared risk, and respects the inherited additive class. The group checks
both directions, the second also in the original adaptive experiment.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the five targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written after the proofs;
they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "ClippingBoundary"
NAMES = ("Specification", "Pointwise", "Kurtosis", "Uniform", "Noise", "NoisyEstimator", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "d5e735c6507a7fba72c2acce2f7e8964cdf9e27fd920574d4a07470499b3e451"
TARGETS = {
    "ClippingBoundary.kurtosis_transfer": "ClippingBoundary.KurtosisTransferStatement",
    "ClippingBoundary.kurtosis_rms": "ClippingBoundary.KurtosisRMSStatement",
    "ClippingBoundary.uniform_clipped_floor": "ClippingBoundary.UniformClippedFloorStatement",
    "ClippingBoundary.noise_counterexample": "ClippingBoundary.NoiseCounterexampleStatement",
    "ClippingBoundary.noisy_estimator": "ClippingBoundary.NoisyEstimatorStatement",
}
COMPONENTS = (
    "ClippingBoundary.quartic_young",
    "ClippingBoundary.seedNoise_probability",
    "ClippingBoundary.variance_seedNoise",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (θ ρ K : ℝ),
    MemLp F 4 P → (∫ ω, F ω ∂P) = θ → 0 ≤ θ → θ ≤ ρ → 1 ≤ K →
    (∫ ω, (F ω - θ) ^ 4 ∂P) ≤ K * ProbabilityTheory.variance F P ^ 2 →
    ENNReal.ofReal (min (ProbabilityTheory.variance F P) (ρ ^ 2) / (256 * K ^ 2)) ≤
      squaredRisk P (fun ω => clipEstimate ρ (F ω)) θ :=
  ClippingBoundary.kurtosis_transfer

example :
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (θ ρ K : ℝ),
    MemLp F 4 P → (∫ ω, F ω ∂P) = θ → 0 ≤ θ → θ ≤ ρ → 1 ≤ K →
    (∫ ω, (F ω - θ) ^ 4 ∂P) ≤ K * ProbabilityTheory.variance F P ^ 2 →
    ENNReal.ofReal (min ρ (Real.sqrt (ProbabilityTheory.variance F P)) / (16 * K)) ≤
      rootMeanRisk P (fun ω => clipEstimate ρ (F ω)) θ :=
  ClippingBoundary.kurtosis_rms

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ρ K : ℝ), 1 ≤ K →
    (∀ q : SignLaw, RarePrior μ ρ q →
      MemLp (populationOutput A) 4 (experimentLaw μ A q) ∧
      (∫ z, populationOutput A z ∂experimentLaw μ A q) = signMean μ q.val ∧
      (∫ z, (populationOutput A z - signMean μ q.val) ^ 4 ∂experimentLaw μ A q) ≤
        K * ProbabilityTheory.variance (populationOutput A) (experimentLaw μ A q) ^ 2) →
    ENNReal.ofReal (1 / (16 * K)) * min (ENNReal.ofReal ρ)
      ((⨆ (q : SignLaw) (_ : RarePrior μ ρ q),
        ProbabilityTheory.evariance (populationOutput A) (experimentLaw μ A q)) ^ (1/2 : ℝ)) ≤
      rareRisk μ (clippedEstimator A ρ) ρ :=
  ClippingBoundary.uniform_clipped_floor

example :
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F₀ : Ω → ℝ) (θ ρ ε M : ℝ),
    MemLp F₀ 2 P → (∫ ω, F₀ ω ∂P) = θ → 0 ≤ θ → θ ≤ ρ → 0 ≤ ε → ε ≤ 1 →
    IsProbabilityMeasure (seedNoise ε M) ∧
    (∫ z, F₀ z.1 + z.2 ∂P.prod (seedNoise ε M)) = θ ∧
    ProbabilityTheory.variance (fun z : Ω × ℝ => F₀ z.1 + z.2) (P.prod (seedNoise ε M)) =
      ProbabilityTheory.variance F₀ P + ε * M ^ 2 ∧
    squaredRisk (P.prod (seedNoise ε M)) (fun z => clipEstimate ρ (F₀ z.1 + z.2)) θ ≤
      squaredRisk P F₀ θ + ENNReal.ofReal (ε * ρ ^ 2) :=
  ClippingBoundary.noise_counterexample

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ε M : ℝ), 0 ≤ ε → ε ≤ 1 →
    ∃ A' : AdaptiveEstimator (R × ℝ),
      A'.randomLaw = A.randomLaw.prod (seedNoise ε M) ∧
      (∀ u, A'.policy u = A.policy u.1) ∧
      (∀ z, A'.output z = A.output (z.1.1, z.2) + z.1.2) ∧
      (∀ q : SignLaw,
        expectedWork μ A' q = expectedWork μ A q ∧
        (Integrable (populationOutput A) (experimentLaw μ A q) →
          Integrable (populationOutput A') (experimentLaw μ A' q) ∧
          (∫ z, populationOutput A' z ∂experimentLaw μ A' q) =
            ∫ z, populationOutput A z ∂experimentLaw μ A q) ∧
        (MemLp (populationOutput A) 2 (experimentLaw μ A q) →
          ProbabilityTheory.variance (populationOutput A') (experimentLaw μ A' q) =
            ProbabilityTheory.variance (populationOutput A) (experimentLaw μ A q) + ε * M ^ 2) ∧
        ∀ θ ρ : ℝ, 0 ≤ θ → θ ≤ ρ →
          squaredRisk (experimentLaw μ A' q) (fun z => clipEstimate ρ (populationOutput A' z)) θ ≤
            squaredRisk (experimentLaw μ A q) (populationOutput A) θ +
              ENNReal.ofReal (ε * ρ ^ 2)) ∧
      (UnbiasedConverse.UniformlyUnbiased μ A → UnbiasedConverse.UniformlyUnbiased μ A') ∧
      (∀ W : ℝ, UniformBudget μ A' W ↔ UniformBudget μ A W) ∧
      (∀ V : ℝ, 0 ≤ V → UnbiasedConverse.UniformVarianceBound μ A V →
        UnbiasedConverse.UniformVarianceBound μ A' (V + ε * M ^ 2)) :=
  ClippingBoundary.noisy_estimator

example : ∀ (s x : ℝ), 0 ≤ s → 3 * s ^ 2 * x ^ 2 ≤ 2 * s ^ 3 * |x| + x ^ 4 :=
  @ClippingBoundary.quartic_young

example : ∀ {ε : ℝ} (M : ℝ), 0 ≤ ε → ε ≤ 1 → IsProbabilityMeasure (seedNoise ε M) :=
  @ClippingBoundary.seedNoise_probability

example : ∀ {ε : ℝ} (M : ℝ), 0 ≤ ε → ε ≤ 1 →
    ProbabilityTheory.variance id (seedNoise ε M) = ε * M ^ 2 :=
  @ClippingBoundary.variance_seedNoise
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
        raise ValueError("Duplicate clipping-boundary declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing clipping-boundary target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed clipping-boundary specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.RareAboveTwo ThresholdHC.RobustContinuation ThresholdHC.ClippingBoundary",
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
    print(f"All {len(TARGETS)} clipping-boundary targets are certified")


if __name__ == "__main__":
    main()
