"""Audit the fixed-plan comparison: the majority-share estimator.

The results guide and the secondary-claims list state, for the toolkit's
fixed plan, that n fresh coins with an odd number m = 2k + 1 of flips each and
the share of coins with a majority of heads have bias at most the mean
misclassification probability e_m and variance at most 1/(4n), uniformly
over the sign laws at a known gap law, so RMS at most sqrt(e_m^2 + 1/(4n));
and that for uniform success rates e_m = binom(2a, a)/2^(2a+1) =
1/(2a Beta(a, 1/2)) with a = k + 1. The group checks these for the plan run
in the original adaptive experiment, with its exact work n(2k+1), and the
uniform integral in binomial-tail form.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the eleven targets and three components with their types written out;
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

GROUP = "FixedPlan"
NAMES = ("Specification", "Tail", "Output", "Risk", "Integral", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "2f64909511db4b10b7d8838e62cee368644b6af013280fd6b54f640e6006871b"
TARGETS = {
    "FixedPlan.majorityWork": "FixedPlan.MajorityWorkStatement",
    "FixedPlan.majorityMissProbability": "FixedPlan.MajorityMissStatement",
    "FixedPlan.majorityMean": "FixedPlan.MajorityMeanStatement",
    "FixedPlan.majorityBias": "FixedPlan.MajorityBiasStatement",
    "FixedPlan.majorityVariance": "FixedPlan.MajorityVarianceStatement",
    "FixedPlan.majorityMSE": "FixedPlan.MajorityMSEStatement",
    "FixedPlan.majorityRMS": "FixedPlan.MajorityRMSStatement",
    "FixedPlan.majorityMinimax": "FixedPlan.MajorityMinimaxStatement",
    "FixedPlan.uniformTailIntegral": "FixedPlan.UniformTailIntegralStatement",
    "FixedPlan.uniformMeanMiss": "FixedPlan.UniformMeanMissStatement",
    "FixedPlan.uniformBeta": "FixedPlan.UniformBetaStatement",
}
COMPONENTS = (
    "FixedPlan.majorityTail_add_symm",
    "FixedPlan.hasDerivAt_majorityTail",
    "FixedPlan.mixture_bias",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ),
    expectedWork μ (majorityEstimator k n) q = ((n*(2*k+1) : ℕ) : ℝ≥0∞) :=
  FixedPlan.majorityWork

example :
  ∀ (k : ℕ) (d : Gap) (s : Bool),
    (tapeMeasure (gapParameter s d)).real {ω | majorityVote k ω ≠ bit s} = majorityMiss k d :=
  FixedPlan.majorityMissProbability

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    (∫ z, populationOutput (majorityEstimator k n) z ∂experimentLaw μ (majorityEstimator k n) q) =
      ∫ d, q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d ∂μ :=
  FixedPlan.majorityMean

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    |(∫ z, populationOutput (majorityEstimator k n) z ∂experimentLaw μ (majorityEstimator k n) q)
      - signMean μ q.val| ≤ meanMajorityMiss μ k :=
  FixedPlan.majorityBias

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    evariance (populationOutput (majorityEstimator k n)) (experimentLaw μ (majorityEstimator k n) q)
      ≤ ENNReal.ofReal (1 / (4 * (n : ℝ))) :=
  FixedPlan.majorityVariance

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    squaredRisk (experimentLaw μ (majorityEstimator k n) q) (populationOutput (majorityEstimator k n))
      (signMean μ q.val) ≤ ENNReal.ofReal (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ))) :=
  FixedPlan.majorityMSE

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ), 0 < n →
    UniformBudget μ (majorityEstimator k n) ((n*(2*k+1) : ℕ) : ℝ) ∧
    maximalRMSRisk μ (majorityEstimator k n) ≤
      ENNReal.ofReal (Real.sqrt (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ)))) :=
  FixedPlan.majorityRMS

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ) (B : ℝ), 0 < n →
    ((n*(2*k+1) : ℕ) : ℝ) ≤ B →
    Tier6.minimaxRisk μ B ≤ ENNReal.ofReal (Real.sqrt (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ)))) :=
  FixedPlan.majorityMinimax

example :
  ∀ k : ℕ, 2 * (∫ p in (0:ℝ)..(1/2), majorityTail k p) =
    ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1) :=
  FixedPlan.uniformTailIntegral

example :
  ∀ k : ℕ, meanMajorityMiss Genie.uniformGapLaw k = ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1) :=
  FixedPlan.uniformMeanMiss

example :
  ∀ k : ℕ, ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1) =
    1 / (2 * ((k : ℝ)+1) * ProbabilityTheory.beta ((k : ℝ)+1) (1/2)) :=
  FixedPlan.uniformBeta

example : ∀ (k : ℕ) (p : ℝ), majorityTail k p + majorityTail k (1-p) = 1 :=
  @FixedPlan.majorityTail_add_symm

example : ∀ (k : ℕ) (p : ℝ),
    HasDerivAt (majorityTail k) ((2*k+1 : ℝ) * ((2*k).choose k : ℝ) * (p*(1-p))^k) p :=
  @FixedPlan.hasDerivAt_majorityTail

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k : ℕ),
    |(∫ d, q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d ∂μ) -
      signMean μ q.val| ≤ meanMajorityMiss μ k :=
  @FixedPlan.mixture_bias
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
        raise ValueError("Duplicate fixed-plan declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing fixed-plan target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed fixed-plan specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailExecution ThresholdHC.FixedPlan",
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
    print(f"All {len(TARGETS)} fixed-plan targets are certified")


if __name__ == "__main__":
    main()
