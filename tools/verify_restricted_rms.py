"""Audit the restricted settings in which the RMS coefficient is exactly 1/6.

The research note rms-gap.tex (research/2026-11-17-rms-constants) finds the
coefficient exactly 1/6 for budgets through four, for protocols with at most
three flips per coin and for two classes with unlimited revisits. Lean's
all-protocol theorem gives 1/6 as a valid coefficient, and the four-fresh-flip
witness at the endpoint gap 1/2 with B = 4 shows nothing larger is valid in
any class that contains it. The targets: the budget restriction 1 <= B <= 4,
the same for both magnitude oracles, a conditional statement for any class
containing every four-fresh-flip protocol, and the three-flip class. The two
unlimited-revisit classes are not defined in Lean; that they contain the
witness is the note's claim.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the four targets and three components with their types written out;
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

GROUP = "RestrictedRMS"
NAMES = ("Specification", "Restricted", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "d130411ba22d1fe6f6b2d11f08e054b5179ad66d237e35ddcc29e6a13953d469"
TARGETS = {
    "RestrictedRMS.small_budget_coefficient": "RestrictedRMS.SmallBudgetCoefficientStatement",
    "RestrictedRMS.oracle_small_budget_coefficient": "RestrictedRMS.OracleSmallBudgetCoefficientStatement",
    "RestrictedRMS.restricted_coefficient": "RestrictedRMS.RestrictedCoefficientStatement",
    "RestrictedRMS.three_flip_coefficient": "RestrictedRMS.ThreeFlipCoefficientStatement",
}
COMPONENTS = (
    "RestrictedRMS.endpoint_modulus_one",
    "RestrictedRMS.four_flips_rms_le",
    "RestrictedRMS.fresh_policy_count",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6 :=
  RestrictedRMS.small_budget_coefficient

example :
  ∀ c : ℝ,
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ revealedMinimaxRisk μ B) ↔ c ≤ 1/6) ∧
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ selectedMinimaxRisk μ B) ↔ c ≤ 1/6) :=
  RestrictedRMS.oracle_small_budget_coefficient

example :
  ∀ (C : ∀ (R : Type) [MeasurableSpace R], AdaptiveEstimator R → Prop) (S : Set ℝ),
    (∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
      (∀ s, A.policy s = freshPolicy 3) → C R A) →
    (∀ B ∈ S, 1 ≤ B) → 4 ∈ S →
    ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), B ∈ S →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤
        sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
          C R A ∧ UniformBudget μ A B ∧ r = maximalRMSRisk μ A}) ↔ c ≤ 1/6 :=
  RestrictedRMS.restricted_coefficient

example :
  ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤
      sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
        (∀ (s : R) (xs : List Bool) (j : ℕ), A.policy s xs = some j →
          (List.range xs.length).countP (fun i => decide (A.policy s (xs.take i) = some j)) < 3) ∧
        UniformBudget μ A B ∧ r = maximalRMSRisk μ A}) ↔ c ≤ 1/6 :=
  RestrictedRMS.three_flip_coefficient

example : modulus (Measure.dirac SharpRMS.endpointGap) (1 / Real.sqrt 4) = 1 :=
  RestrictedRMS.endpoint_modulus_one

example : maximalRMSRisk (Measure.dirac SharpRMS.endpointGap) SharpRMS.fourFlips ≤
    ENNReal.ofReal (1/6 : ℝ) :=
  RestrictedRMS.four_flips_rms_le

example : ∀ (xs : List Bool) (j : ℕ), freshPolicy 3 xs = some j →
    (List.range xs.length).countP (fun i => decide (freshPolicy 3 (xs.take i) = some j)) < 3 :=
  RestrictedRMS.fresh_policy_count
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
        raise ValueError("Duplicate restricted RMS declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing restricted RMS target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed restricted RMS specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower",
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
    print(f"All {len(TARGETS)} restricted RMS targets are certified")


if __name__ == "__main__":
    main()
