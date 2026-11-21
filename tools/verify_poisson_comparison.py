"""Audit the Poisson case of the RMS affine comparison lemma.

Lemma lem:comparison of the nonlinear-critical research package compares an
arbitrary estimator with the best additive one in a finite convex experiment,
in a categorical case and a Poisson case, with constant 12. The categorical
case is the AffineComparison group. This group states the Poisson case: for
independent Poisson counts with intensities affine in the parameter and
strictly positive on a nonempty compact convex set, an estimator with squared
risk at most r^2 everywhere on the set yields, for every eta > 0, an additive
estimator with squared risk at most (C r + eta)^2 there, for C = 6 (a
sharpening by the Lean route) and C = 12 (the source's constant). The
components pin the Poisson vector law: it is a probability law, its
exponential moments, and the Hellinger affinity of two such laws; and the
statement fails for C = 1/2.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and five components with their types written out;
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

GROUP = "PoissonComparison"
NAMES = ("Specification", "Law", "LogMoment", "Affinity", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "e630678d642d72cc6806022bf7368315852d0beb231f24a740692b2686466b78"
TARGETS = {
    "PoissonComparison.poisson_comparison_6": "PoissonComparison.PoissonComparisonStatement",
    "PoissonComparison.poisson_comparison_12": "PoissonComparison.PoissonComparisonStatement",
}
COMPONENTS = (
    "PoissonComparison.poissonVectorLaw_isProbabilityMeasure",
    "PoissonComparison.poissonVectorLaw_exp_integral",
    "PoissonComparison.poissonVectorLaw_exp_integrable",
    "PoissonComparison.poissonVectorLaw_affinity",
    "PoissonComparison.poisson_comparison_not_half",
)
# The statement takes the constant as its argument.
TARGET_ARGS = {
    "PoissonComparison.poisson_comparison_6": "6",
    "PoissonComparison.poisson_comparison_12": "12",
}
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E), X.Nonempty → IsCompact X → Convex ℝ X →
  ∀ (J : Type) [Fintype J] (v : E →ᵃ[ℝ] (J → ℝ)) (ell : E →ᵃ[ℝ] ℝ),
    (∀ x ∈ X, ∀ j, 0 < v x j) →
  ∀ (G : (J → ℕ) → ℝ) (r : ℝ), 0 ≤ r →
    (∀ x ∈ X, squaredRisk (poissonVectorLaw (v x)) G (ell x) ≤ ENNReal.ofReal (r^2)) →
  ∀ η : ℝ, 0 < η → ∃ (β : J → ℝ) (c : ℝ), ∀ x ∈ X,
    squaredRisk (poissonVectorLaw (v x)) (fun z => c + ∑ j, β j * (z j : ℝ)) (ell x) ≤
      ENNReal.ofReal ((6*r+η)^2) :=
  PoissonComparison.poisson_comparison_6

example :
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E), X.Nonempty → IsCompact X → Convex ℝ X →
  ∀ (J : Type) [Fintype J] (v : E →ᵃ[ℝ] (J → ℝ)) (ell : E →ᵃ[ℝ] ℝ),
    (∀ x ∈ X, ∀ j, 0 < v x j) →
  ∀ (G : (J → ℕ) → ℝ) (r : ℝ), 0 ≤ r →
    (∀ x ∈ X, squaredRisk (poissonVectorLaw (v x)) G (ell x) ≤ ENNReal.ofReal (r^2)) →
  ∀ η : ℝ, 0 < η → ∃ (β : J → ℝ) (c : ℝ), ∀ x ∈ X,
    squaredRisk (poissonVectorLaw (v x)) (fun z => c + ∑ j, β j * (z j : ℝ)) (ell x) ≤
      ENNReal.ofReal ((12*r+η)^2) :=
  PoissonComparison.poisson_comparison_12

example : ∀ {J : Type} [Fintype J] (w : J → ℝ), IsProbabilityMeasure (PoissonComparison.poissonVectorLaw w) :=
  @PoissonComparison.poissonVectorLaw_isProbabilityMeasure

example : ∀ {J : Type} [Fintype J] (w : J → ℝ), (∀ j, 0 ≤ w j) → ∀ (b : ℝ) (β : J → ℝ), (∫ z, Real.exp (b + ∑ j, β j * (z j : ℝ)) ∂(PoissonComparison.poissonVectorLaw w)) = Real.exp (b + ∑ j, w j * (Real.exp (β j) - 1)) :=
  @PoissonComparison.poissonVectorLaw_exp_integral

example : ∀ {J : Type} [Fintype J] (w : J → ℝ) (b : ℝ) (β : J → ℝ), Integrable (fun z : J → ℕ => Real.exp (b + ∑ j, β j * (z j : ℝ))) (PoissonComparison.poissonVectorLaw w) :=
  @PoissonComparison.poissonVectorLaw_exp_integrable

example : ∀ {J : Type} [Fintype J] (w w' : J → ℝ), (∀ j, 0 < w j) → (∀ j, 0 < w' j) → (CriticalEntropy.hellingerAffinity (PoissonComparison.poissonVectorLaw w) (PoissonComparison.poissonVectorLaw w')).toReal = Real.exp (-(∑ j, (Real.sqrt (w j) - Real.sqrt (w' j))^2)/2) :=
  @PoissonComparison.poissonVectorLaw_affinity

example : ¬ PoissonComparison.PoissonComparisonStatement (1/2) :=
  PoissonComparison.poisson_comparison_not_half
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
        raise ValueError("Duplicate poisson-comparison declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing poisson-comparison target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed poisson-comparison specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.PoissonComparison",
        *[f"example : {statement} {TARGET_ARGS[theorem]} := {theorem}"
          for theorem, statement in sorted(TARGETS.items())],
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
    print(f"All {len(TARGETS)} poisson-comparison targets are certified")


if __name__ == "__main__":
    main()
