"""Audit the stopped time-uniform remark.

For 0 < rho <= 1/4 and 0 < delta <= 1/4:

* Prefix confidence: every estimate formed from the private seed and the first
  n >= 1 physical observations, with failure probability at most delta at
  radius eps under every rare sign law, has eps >= 10^-17 K(n/log(1/delta)),
  the fixed-budget coefficient.
* Stopped fixed budget: so every time-uniform interval procedure with joint
  coverage and half-width envelope t has t_n >= 10^-17 K(n/log(1/delta)) at
  every n >= 1.
* The remark: display (TU1), t_n >= 10^-22 K(n/Lambda_n), holds at every
  n >= 2 with log log n <= (10^10 - 1) log(1/delta).

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
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

GROUP = "StoppedTimeUniform"
NAMES = ("Specification", "Prefix", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "f57110e5d2dd60b122bcf7b4153ccff6d5880aaa08dd8eb554b513e9394d7f2c"
TARGETS = {
    "StoppedTimeUniform.prefix_confidence": "StoppedTimeUniform.PrefixConfidenceStatement",
    "StoppedTimeUniform.stopped_fixed_budget": "StoppedTimeUniform.StoppedFixedBudgetStatement",
    "StoppedTimeUniform.stopped_time_uniform": "StoppedTimeUniform.StoppedTimeUniformStatement",
}
COMPONENTS = (
    "StoppedTimeUniform.prefix_pair_work",
    "StoppedTimeUniform.coverage_prefix_failure",
    "StoppedTimeUniform.inflation_selection",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ ε : ℝ) (n : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 → 0 ≤ ε → 0 < n →
    ∀ (A : AdaptiveEstimator R) (H : R × Tier3.Prefix n → ℝ), Measurable H →
      (∀ q : SignLaw, RarePrior μ ρ q →
        (observablePrefixLaw μ A q n) {x | ε < |H x - signMean μ q.val|} ≤ ENNReal.ofReal δ) →
      ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) *
          EntropyTail.selection μ ρ ((n : ℝ) / Real.log (1/δ)) ≤ ENNReal.ofReal ε :=
  StoppedTimeUniform.prefix_confidence

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    ∀ (A : AdaptiveEstimator R) (L U : ∀ n, R × Tier3.Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → AnytimeLower.OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ n : ℕ, 0 < n →
        (10 : ℝ)⁻¹ ^ 17 *
          (EntropyTail.selection μ ρ ((n : ℝ) / Real.log (1/δ))).toReal ≤ t n :=
  StoppedTimeUniform.stopped_fixed_budget

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    ∀ (A : AdaptiveEstimator R) (L U : ∀ n, R × Tier3.Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → AnytimeLower.OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ n : ℕ, 2 ≤ n → Real.log (Real.log (n : ℝ)) ≤ ((10 : ℝ) ^ 10 - 1) * Real.log (1/δ) →
        (10 : ℝ)⁻¹ ^ 22 *
          (EntropyTail.selection μ ρ ((n : ℝ) / AnytimeLower.budgetInflation δ n)).toReal ≤ t n :=
  StoppedTimeUniform.stopped_time_uniform

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {n : ℕ} (H : R × Tier3.Prefix n → ℝ), Measurable H →
    ∀ (q r : SignLaw) {ρ κ ε δ : ℝ}, 0 ≤ κ → 0 < δ → δ ≤ 1/4 →
    RarePrior μ ρ q → RarePrior μ ρ r →
    ConfidenceTransfer.LocalReferenceWorkBound μ (ObservableSimulation.gapParameter false)
      (ObservableSimulation.gapParameter true) (ObservableSimulation.signUnit q)
      (ObservableSimulation.signUnit r) κ →
    (∀ s : SignLaw, RarePrior μ ρ s →
      (observablePrefixLaw μ A s n) {x | ε < |H x - signMean μ s.val|} ≤ ENNReal.ofReal δ) →
    4*ε < signMean μ q.val - signMean μ r.val →
    Real.log (1/δ)/4 ≤ (8/3)*κ*n :=
  @StoppedTimeUniform.prefix_pair_work

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (L U : ∀ n, R × Tier3.Prefix n → ℝ),
    (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) → ∀ {ρ δ : ℝ} (t : ℕ → ℝ),
    AnytimeLower.OnlineIntervalCoverage μ A L U ρ δ t → ∀ (n : ℕ) (q : SignLaw), RarePrior μ ρ q →
    (observablePrefixLaw μ A q n) {x | t n < |(L n x + U n x)/2 - signMean μ q.val|} ≤
      ENNReal.ofReal δ :=
  @StoppedTimeUniform.coverage_prefix_failure

example : ∀ {μ : Measure Gap} {ρ δ : ℝ}, 0 < δ → δ ≤ 1/4 → ∀ {n : ℕ}, 2 ≤ n →
    Real.log (Real.log (n : ℝ)) ≤ ((10 : ℝ) ^ 10 - 1) * Real.log (1/δ) →
    EntropyTail.selection μ ρ ((n : ℝ) / AnytimeLower.budgetInflation δ n) ≤
      ENNReal.ofReal ((10 : ℝ) ^ 5) * EntropyTail.selection μ ρ ((n : ℝ) / Real.log (1/δ)) :=
  @StoppedTimeUniform.inflation_selection
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
        raise ValueError("Duplicate stopped time-uniform declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing stopped time-uniform target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed stopped time-uniform specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo",
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
    print(f"All {len(TARGETS)} stopped time-uniform targets are certified")


if __name__ == "__main__":
    main()
