"""Audit the explicit odd-Legendre pair of the bounded-depth obstruction.

Lemma lem:poly and Theorem thm:cap of
research/2026-10-27-nonlinear-population/upper/proof-body.tex: for K >= 1 the
normalized odd Legendre polynomial u_K = P_{2K+1}/(c x) is even of degree 2K,
bounded by one on [0,1], orthogonal to x^(2j+2) for j < K, with
int_0^1 2x u_K = 1/((K+1)(2K+1)). On the exact quadratic law the allocations
q_pm = (1 pm u_K(d/h))/2 on d <= h = a sqrt(rho) are rare, have targets
rho/2 (1 pm m_K) and give every coin word of length at most 2K the same
probability, so every procedure obeying the per-coin cap 2K, with arbitrary
feedback, has the same seed-and-transcript law under both and RMS error at
least rho/(2(K+1)(2K+1)). Part 1, the floor for any matching pair, is the
group DepthObstruction; the depth-tail bound thm:tail is not stated.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and four components with their types written out;
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

GROUP = "DepthLegendre"
NAMES = ("Specification", "Rodrigues", "Polynomial", "Energy", "Moments", "QuadraticLaw", "Pair", "Floor", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "613cf66f3912253054aaaec1f22e3eda20a4900448f0d1a92ddee3dce69a4869"
TARGETS = {
    "DepthLegendre.depth_polynomial": "DepthLegendre.DepthPolynomialStatement",
    "DepthLegendre.depth_pair": "DepthLegendre.DepthPairStatement",
    "DepthLegendre.depth_cap_floor": "DepthLegendre.DepthCapFloorStatement",
}
COMPONENTS = (
    "DepthLegendre.legendre_ode",
    "DepthLegendre.legendre_eval_one",
    "DepthLegendre.abs_depthSlope_ge_one",
    "DepthLegendre.quadratic_cut_integral",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ K : ℕ, 1 ≤ K →
    depthSlope K ≠ 0 ∧
    (∀ x : ℝ, x ≠ 0 →
      (depthPolynomial K).eval x = (legendre (2*K+1)).eval x / (depthSlope K * x)) ∧
    (depthPolynomial K).eval 0 = 1 ∧
    (depthPolynomial K).natDegree = 2*K ∧
    (∀ x : ℝ, (depthPolynomial K).eval (-x) = (depthPolynomial K).eval x) ∧
    (∀ x ∈ Set.Icc (0:ℝ) 1, |(depthPolynomial K).eval x| ≤ 1) ∧
    (∀ j < K, ∫ x in (0:ℝ)..1, x^(2*j+2) * (depthPolynomial K).eval x = 0) ∧
    ∫ x in (0:ℝ)..1, 2*x*(depthPolynomial K).eval x = depthMoment K :=
  DepthLegendre.depth_polynomial

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ : ℝ) (K : ℕ),
    0 < a → a < 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ K → ExactPowerLaw μ 2 a →
    ∃ qH qL : SignLaw, qH.val = depthSign K a ρ true ∧ qL.val = depthSign K a ρ false ∧
      RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      signMean μ qH.val = ρ/2 * (1 + depthMoment K) ∧
      signMean μ qL.val = ρ/2 * (1 - depthMoment K) ∧
      signMean μ qH.val - signMean μ qL.val = ρ / (((K:ℝ)+1) * (2*K+1)) ∧
      OddMomentMatch μ qH qL (2*K) ∧
      (∀ n k : ℕ, n ≤ 2*K → k ≤ n →
        populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit qH) n k =
          populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit qL) n k) ∧
      ρ / (((K:ℝ)+1) * (2*K+1)) ≤ capDiameter μ ρ (2*K) :=
  DepthLegendre.depth_pair

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (a ρ : ℝ) (K : ℕ) (A : AdaptiveEstimator R),
    0 < a → a < 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ K → ExactPowerLaw μ 2 a → PerCoinCap A (2*K) →
    (∃ qH qL : SignLaw, qH.val = depthSign K a ρ true ∧ qL.val = depthSign K a ρ false ∧
      RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      (experimentLaw μ A qH).map (fun z => (z.1.1, z.2)) =
        (experimentLaw μ A qL).map (fun z => (z.1.1, z.2)) ∧
      ENNReal.ofReal (ρ / (2*((K:ℝ)+1)*(2*K+1))) ≤
        max (rootMeanRisk (experimentLaw μ A qH) (populationOutput A) (signMean μ qH.val))
            (rootMeanRisk (experimentLaw μ A qL) (populationOutput A) (signMean μ qL.val))) ∧
    ENNReal.ofReal (ρ / (2*((K:ℝ)+1)*(2*K+1))) ≤ rareRisk μ A ρ :=
  DepthLegendre.depth_cap_floor

example : ∀ n : ℕ, (X^2-1) * derivative^[2] (legendre n) + 2*X * derivative (legendre n) -
    C ((n:ℝ)*(n+1)) * legendre n = 0 :=
  DepthLegendre.legendre_ode

example : ∀ n : ℕ, (legendre n).eval 1 = 1 :=
  DepthLegendre.legendre_eval_one

example : ∀ K : ℕ, 1 ≤ |depthSlope K| :=
  DepthLegendre.abs_depthSlope_ge_one

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ : ℝ},
    0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1 → ExactPowerLaw μ 2 a →
    ∀ (G : ℝ → ℝ), Continuous G →
    ∫ d, (if (d:ℝ) ≤ a * Real.sqrt ρ then G ((d:ℝ) / (a * Real.sqrt ρ)) else 0) ∂μ =
      ∫ x in (0:ℝ)..1, 2 * ρ * x * G x :=
  @DepthLegendre.quadratic_cut_integral
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
        raise ValueError("Duplicate depth-legendre declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing depth-legendre target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed depth-legendre specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open Polynomial ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CapIdentification ThresholdHC.DepthObstruction ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.DepthLegendre",
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
    print(f"All {len(TARGETS)} depth-legendre targets are certified")


if __name__ == "__main__":
    main()
