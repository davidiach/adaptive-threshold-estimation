"""Audit the categorical case of the RMS affine comparison lemma.

Lemma lem:comparison of research/2026-10-27-nonlinear-critical/affine_comparison.tex
(case 1) says: for independent finite categorical observations whose
probability vectors are affine in a parameter x ranging over a nonempty
compact convex set, and an affine target, if some estimator has RMS risk at
most r at every parameter, then for every eta > 0 an additive estimator
c + sum_i phi_i(z_i) has RMS risk at most 12 r + eta at every parameter.
The group proves it with the constant 6, a sharpening obtained by the Lean
route only (an affinity testing bound in place of the source's
total-variation test), and the source's 12 as a corollary. The Poisson case
of the lemma is not stated.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and three components with their types written out;
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

GROUP = "AffineComparison"
NAMES = ("Specification", "Saddle", "Moments", "Categorical", "Testing", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "e8d3833a6deeefca8dacb3fb51c9672d8a3a948c954c6c3f3b8cd5a3582c6a42"
TARGETS = {
    "AffineComparison.categorical_comparison_6": "AffineComparison.CategoricalComparisonStatement",
    "AffineComparison.categorical_comparison_12": "AffineComparison.CategoricalComparisonStatement",
}
COMPONENTS = (
    "AffineComparison.categoricalProductLaw_affinity",
    "AffineComparison.difference_le_of_affinity",
    "AffineComparison.categoricalLaw_isProbabilityMeasure",
)
# The statement takes the constant as its argument.
TARGET_ARGS = {
    "AffineComparison.categorical_comparison_6": "6",
    "AffineComparison.categorical_comparison_12": "12",
}
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E), X.Nonempty → IsCompact X → Convex ℝ X →
  ∀ (k : ℕ) (I : Fin k → Type) [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)]
    [∀ i, MeasurableSingletonClass (I i)]
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (ell : E →ᵃ[ℝ] ℝ),
    (∀ x ∈ X, ∀ i a, 0 < p i x a) → (∀ x ∈ X, ∀ i, ∑ a, p i x a = 1) →
  ∀ (G : (∀ i, I i) → ℝ) (r : ℝ), 0 ≤ r →
    (∀ x ∈ X, squaredRisk (categoricalProductLaw (fun i => p i x)) G (ell x) ≤
      ENNReal.ofReal (r^2)) →
  ∀ η : ℝ, 0 < η → ∃ (φ : ∀ i, I i → ℝ) (c : ℝ), ∀ x ∈ X,
    squaredRisk (categoricalProductLaw (fun i => p i x))
      (fun z => c + ∑ i, φ i (z i)) (ell x) ≤ ENNReal.ofReal ((6*r+η)^2) :=
  AffineComparison.categorical_comparison_6

example :
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E), X.Nonempty → IsCompact X → Convex ℝ X →
  ∀ (k : ℕ) (I : Fin k → Type) [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)]
    [∀ i, MeasurableSingletonClass (I i)]
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (ell : E →ᵃ[ℝ] ℝ),
    (∀ x ∈ X, ∀ i a, 0 < p i x a) → (∀ x ∈ X, ∀ i, ∑ a, p i x a = 1) →
  ∀ (G : (∀ i, I i) → ℝ) (r : ℝ), 0 ≤ r →
    (∀ x ∈ X, squaredRisk (categoricalProductLaw (fun i => p i x)) G (ell x) ≤
      ENNReal.ofReal (r^2)) →
  ∀ η : ℝ, 0 < η → ∃ (φ : ∀ i, I i → ℝ) (c : ℝ), ∀ x ∈ X,
    squaredRisk (categoricalProductLaw (fun i => p i x))
      (fun z => c + ∑ i, φ i (z i)) (ell x) ≤ ENNReal.ofReal ((12*r+η)^2) :=
  AffineComparison.categorical_comparison_12

example : ∀ {k : ℕ} {I : Fin k → Type} [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)]
    [∀ i, MeasurableSingletonClass (I i)] (q q' : ∀ i, I i → ℝ),
    (∀ i a, 0 ≤ q i a) → (∀ i a, 0 ≤ q' i a) →
    (hellingerAffinity (categoricalProductLaw q) (categoricalProductLaw q')).toReal =
      ∏ i, realFiniteAffinity (q i) (q' i) :=
  @AffineComparison.categoricalProductLaw_affinity

example : ∀ {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (f : Ω → ℝ), Measurable f → ∀ (a b r : ℝ), 0 ≤ r →
    squaredRisk P f a ≤ ENNReal.ofReal (r^2) → squaredRisk Q f b ≤ ENNReal.ofReal (r^2) →
    1/2 ≤ (hellingerAffinity P Q).toReal → a-b ≤ 4*r :=
  @AffineComparison.difference_le_of_affinity

example : ∀ {I : Type} [Fintype I] [MeasurableSpace I] (q : I → ℝ),
    (∀ a, 0 ≤ q a) → ∑ a, q a = 1 → IsProbabilityMeasure (categoricalLaw q) :=
  @AffineComparison.categoricalLaw_isProbabilityMeasure
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
        raise ValueError("Duplicate affine-comparison declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing affine-comparison target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed affine-comparison specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.AffineComparison",
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
    print(f"All {len(TARGETS)} affine-comparison targets are certified")


if __name__ == "__main__":
    main()
