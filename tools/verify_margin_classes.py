"""Audit the margin-class corollaries of the v6 manuscript.

Corollary cor:gap and the rows alpha < 1 and alpha > 1 of Corollary cor:power:
explicit two-sided bounds on the smallest uniform expected-work budget of an
(eps, delta)-valid estimator over the gap class G_Delta and the polynomial
margin class G_{alpha,C} (2^alpha <= C), for eps <= 1/25 and 0 < delta <= 1/4;
the unbiased dichotomy on the whole margin class (an unbiased estimator with
finite uniform variance and work exists iff alpha > 1); one common unbiased
estimator chosen before alpha and C; and one budget-indexed family chosen
before the class parameters that attains all three upper budgets. The
critical row alpha = 1, cor:log and the rate table are not stated.

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

GROUP = "MarginClasses"
NAMES = ("Specification", "Basic", "Gap", "Power", "Unbiased", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "51be0bccd5c78ca63daa105bc8e997cd3ccb3d644cfaf8457a8f8cdc4fd9b8d4"
TARGETS = {
    "MarginClasses.gap_class": "MarginClasses.GapClassStatement",
    "MarginClasses.sublinear_class": "MarginClasses.SublinearClassStatement",
    "MarginClasses.superlinear_class": "MarginClasses.SuperlinearClassStatement",
    "MarginClasses.power_unbiased": "MarginClasses.PowerUnbiasedStatement",
    "MarginClasses.common_unbiased": "MarginClasses.CommonUnbiasedStatement",
    "MarginClasses.common_confidence": "MarginClasses.CommonConfidenceStatement",
}
COMPONENTS = (
    "MarginClasses.valid_budget_ge_one",
    "MarginClasses.cutoff_lt",
    "MarginClasses.dirac_gapClass",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ Δ ε δ : ℝ, 0 < Δ → Δ ≤ 1/2 → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (225/131072 * Real.log (1/δ) / (ε^2 * Δ^2)) ≤ classWork (GapClass Δ) ε δ ∧
    classWork (GapClass Δ) ε δ ≤ ENNReal.ofReal (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) :=
  MarginClasses.gap_class

example :
  ∀ α C ε δ : ℝ, 0 < α → α < 1 → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal ((15 * C / (256 * Real.sqrt 2)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α))
        ≤ classWork (PowerClass α C) ε δ ∧
      classWork (PowerClass α C) ε δ ≤
        ENNReal.ofReal ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) :=
  MarginClasses.sublinear_class

example :
  ∀ α C ε δ : ℝ, 1 < α → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (225/32768 * Real.log (1/δ) / ε^2) ≤ classWork (PowerClass α C) ε δ ∧
      classWork (PowerClass α C) ε δ ≤
        ENNReal.ofReal ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) :=
  MarginClasses.superlinear_class

example :
  ∀ α C : ℝ, 0 < α → 2 ^ α ≤ C →
    ((∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (V W : ℝ), 0 ≤ V ∧ 0 ≤ W ∧
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
        UniformlyUnbiased ν A ∧ UniformVarianceBound ν A V ∧ UniformBudget ν A W) ↔ 1 < α) :=
  MarginClasses.power_unbiased

example :
  ∃ A : AdaptiveEstimator ℕ, ∀ α C : ℝ, 1 < α → 2 ^ α ≤ C →
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
      UniformlyUnbiased ν A ∧
      UniformVarianceBound ν A (23 * (α * C ^ (1/α) / (α - 1))) ∧
      UniformBudget ν A (31 * (α * C ^ (1/α) / (α - 1))) :=
  MarginClasses.common_unbiased

example :
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → AdaptiveEstimator R),
    (∀ Δ ε δ : ℝ, 0 < Δ → Δ ≤ 1/2 → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], GapClass Δ ν →
        UniformBudget ν (rule (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) δ)
            (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) ∧
        UniformConfidence ν (rule (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) δ) ε δ) ∧
    (∀ α C ε δ : ℝ, 0 < α → α < 1 → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
        UniformBudget ν (rule ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) δ)
            ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) ∧
        UniformConfidence ν
          (rule ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) δ) ε δ) ∧
    (∀ α C ε δ : ℝ, 1 < α → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
        UniformBudget ν (rule ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) δ)
            ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) ∧
        UniformConfidence ν
          (rule ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) δ) ε δ) :=
  MarginClasses.common_confidence

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {B ε δ : ℝ}, 0 ≤ ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
    UniformBudget μ A B → UniformConfidence μ A ε δ → 1 ≤ B :=
  @MarginClasses.valid_budget_ge_one

example : (1:ℝ)/25 < 15/(256*Real.sqrt 2) :=
  MarginClasses.cutoff_lt

example : ∀ {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1/2),
    GapClass Δ (Measure.dirac (⟨Δ,hΔ,hΔ'⟩ : Gap)) :=
  @MarginClasses.dirac_gapClass
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
        raise ValueError("Duplicate margin-classes declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing margin-classes target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed margin-classes specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.UnbiasedConverse ThresholdHC.MarginClasses",
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
    print(f"All {len(TARGETS)} margin-classes targets are certified")


if __name__ == "__main__":
    main()
