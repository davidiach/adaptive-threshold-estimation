"""Audit the two-sided time-uniform order in one model.

The time-uniform upper theorem of Appendix app:anytime of the v6 manuscript
(Lean: ThresholdHC.Anytime.known_anytime) is stated for a budget-indexed
family of stage controllers under its own stream law; the law-dependent lower
bound (TU1) (ThresholdHC.AnytimeLower.law_dependent_interval_lower) for one
online policy in the original observable experiment. This group runs the
stage family as one online policy in that experiment, with an interval at
every integer budget n that reads the seed and the first n observations, joint
coverage and width control at most 1500002 K(n/Lambda(n,delta)) for n >= 1 and
3000004 K(n/lambda(n)) for n >= 3; together with the lower bound, the
half-width has order K(n/lambda(n)) in one model, between 10^-22 (at
arbitrarily late budgets) and 3000004. Nesting of the intervals, real budgets
and the per-budget flip cap are not restated.

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

GROUP = "TimeUniformTwoSided"
NAMES = ("Specification", "Online", "Scale", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "1b1fcf68e7bd744a33b406591a580a98abe4aa04383d3c9a83c940d3584c683b"
TARGETS = {
    "TimeUniformTwoSided.online_upper": "TimeUniformTwoSided.OnlineUpperStatement",
    "TimeUniformTwoSided.time_uniform_two_sided": "TimeUniformTwoSided.TimeUniformTwoSidedStatement",
}
COMPONENTS = (
    "TimeUniformTwoSided.inflation_le_four",
    "TimeUniformTwoSided.envelope_scale",
    "TimeUniformTwoSided.onlineInterval_readback",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R)
      (L U : ∀ n, R × Prefix n → ℝ) (t : ℕ → ℝ),
      (∀ n, Measurable (L n)) ∧ (∀ n, Measurable (U n)) ∧ (∀ n, 0 ≤ t n) ∧
      OnlineIntervalCoverage μ A L U ρ δ t ∧
      (∀ n : ℕ, 1 ≤ n → t n ≤ 1500002 *
        (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) /
          (Real.log (1/δ) + 2 * Real.log (2 + Real.log (1 + (n : ℝ)) / Real.log 2)))).toReal) ∧
      (∀ n : ℕ, 3 ≤ n → t n ≤ 3000004 *
        (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal) :=
  TimeUniformTwoSided.online_upper

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    (∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R)
        (L U : ∀ n, R × Prefix n → ℝ) (t : ℕ → ℝ),
        (∀ n, Measurable (L n)) ∧ (∀ n, Measurable (U n)) ∧ (∀ n, 0 ≤ t n) ∧
        OnlineIntervalCoverage μ A L U ρ δ t ∧
        (∀ n : ℕ, 3 ≤ n → t n ≤ 3000004 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal) ∧
        (∀ M : ℕ, ∃ n : ℕ, max M 3 ≤ n ∧ (10 : ℝ)⁻¹ ^ 22 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal ≤ t n)) ∧
    (∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ M : ℕ, ∃ n : ℕ, max M 3 ≤ n ∧ (10 : ℝ)⁻¹ ^ 22 *
        (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal ≤ t n) :=
  TimeUniformTwoSided.time_uniform_two_sided

example : ∀ {δ : ℝ}, 0 < δ → δ ≤ 1/4 → ∀ {n : ℕ}, 3 ≤ n →
    ThresholdHC.Anytime.inflation (n:ℝ) δ ≤ 4*budgetInflation δ n :=
  @TimeUniformTwoSided.inflation_le_four

example : ∀ (μ : Measure Gap) (ρ : ℝ) {δ : ℝ}, 0 < δ → δ ≤ 1/4 → ∀ {n : ℕ}, 3 ≤ n →
    1500002*(ThresholdHC.EntropyTail.selection μ ρ
        ((n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ)).toReal ≤
      3000004*(ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n)).toReal :=
  @TimeUniformTwoSided.envelope_scale

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (base : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (radius : ℕ → ℝ) (n : ℕ) (z : (∀ j, R j) × Table),
    TimeUniformTwoSided.onlineInterval base M radius n
        (z.1,processPrefix n (populationPath ((TimeUniformTwoSided.limitEstimator base).policy z.1) z.2)) =
      ThresholdHC.Anytime.observedInterval base M radius (stageCount (n:ℝ)) z :=
  @TimeUniformTwoSided.onlineInterval_readback
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
        raise ValueError("Duplicate time-uniform-two-sided declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing time-uniform-two-sided target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed time-uniform-two-sided specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.AnytimeLower ThresholdHC.HardBudget ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper",
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
    print(f"All {len(TARGETS)} time-uniform-two-sided targets are certified")


if __name__ == "__main__":
    main()
