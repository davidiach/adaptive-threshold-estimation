"""Audit the decimal bounds and remarks of the appendix on the upper constant 12.

The appendix app:upper-12 of paper/v6/appendix-upper-constant.tex uses
decimal intermediate bounds whose rational versions Lean already checks
(26/5, 41/100, 13/2), and closes with three remarks comparing upper-bound
routes. Its verification paragraph lists both as not Lean-checked. The group
checks the decimal bounds (1-r) sum_j r^j C_j sqrt v_j < 5.19, the wrong-side
constant < 0.401 and the second-moment constant < 6.49, each on the paper's
expression and, for the last two, on the operational sums; and the remarks
for the specific families: the two-level mixture pays 9/2, with constant
sqrt((9/2)(174/5)) in (12.51, 12.52); the dyadic batch pays B/2^L < 8 with
supremum 8, with RMS at most sqrt(8 * 174/5) omega; the calibration at scale
B/4 pays 4 and its call's squared bias is at most lambda omega((B/4)^-1/2)^2
with 1 <= lambda < 2. The approximate values 5.182, 5.185 and 1.762 are not
stated.

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

GROUP = "UpperTwelveNumerics"
NAMES = ("Specification", "CallCost", "WrongSide", "SecondMoment", "Remarks", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "49ef5f38bd5c169c13c8e08564e7727ad23071cf267b2ef5e223623d2192ab19"
TARGETS = {
    "UpperTwelveNumerics.call_cost_decimal": "UpperTwelveNumerics.CallCostDecimalStatement",
    "UpperTwelveNumerics.wrong_side_decimal": "UpperTwelveNumerics.WrongSideDecimalStatement",
    "UpperTwelveNumerics.second_moment_decimal": "UpperTwelveNumerics.SecondMomentDecimalStatement",
    "UpperTwelveNumerics.mixture_remark": "UpperTwelveNumerics.MixtureRemarkStatement",
    "UpperTwelveNumerics.dyadic_batch": "UpperTwelveNumerics.DyadicBatchStatement",
    "UpperTwelveNumerics.scale_four_bias": "UpperTwelveNumerics.ScaleFourBiasStatement",
}
COMPONENTS = (
    "UpperTwelveNumerics.callCost_tsum_le",
    "UpperTwelveNumerics.wrongSideConstant_lt",
    "UpperTwelveNumerics.dyadic_ratio_lt",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  Summable callCostTerm ∧ ∑' j, callCostTerm j < 519/100 :=
  UpperTwelveNumerics.call_cost_decimal

example :
  wrongSideConstant < 401/1000 ∧
  ∀ (L : ℕ) (d : ℝ), 0 < d →
    d * ∑ l ∈ range (L + 1),
        (UpperDisagreement.stopError l d + UpperDisagreement.stopError (l - 1) d) / pLevel l
      ≤ wrongSideConstant :=
  UpperTwelveNumerics.wrong_side_decimal

example :
  (2 + Real.sqrt 2) * (89/50) + 41/100 < (649/100 : ℝ) ∧
  ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    d * secondMomentK 1 1 L d S ≤ (2 + Real.sqrt 2) * (89/50) + 41/100 :=
  UpperTwelveNumerics.second_moment_decimal

example :
  (1251/100 : ℝ) < Real.sqrt ((9/2) * (174/5)) ∧ Real.sqrt ((9/2) * (174/5)) < 1252/100 ∧
  ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    UniformBudget μ (UpperMixture.budgetMixture B) B ∧
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (Real.sqrt ((9/2) * (174/5)) * modulus μ (1 / Real.sqrt B)) :=
  UpperTwelveNumerics.mixture_remark

example :
  (∀ B : ℝ, 4 ≤ B → B / (2 : ℝ) ^ BlindUpper.budgetLevel B < 8) ∧
  (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 4 ≤ B ∧ 8 - ε < B / (2 : ℝ) ^ BlindUpper.budgetLevel B) ∧
  ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    UniformBudget μ (BlindUpper.budgetEstimator B) B ∧
    maximalRMSRisk μ (BlindUpper.budgetEstimator B) ≤
      ENNReal.ofReal (Real.sqrt (8 * (174/5)) * modulus μ (1 / Real.sqrt B)) :=
  UpperTwelveNumerics.dyadic_batch

example :
  ∀ B : ℝ, 4 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    1 ≤ B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) ∧
    B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) < 2 ∧
    ((∫ z, BlindUpper.cutoffValue (BlindUpper.budgetLevel B) z ∂BlindUpper.callMeasure μ q) -
        signMean μ q.val) ^ 2 ≤
      B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) * modulus μ (1 / Real.sqrt (B / 4)) ^ 2 ∧
    modulus μ (1 / Real.sqrt (B / 4)) ^ 2 ≤ 4 * modulus μ (1 / Real.sqrt B) ^ 2 :=
  UpperTwelveNumerics.scale_four_bias

example : ∑' j, callCostTerm j ≤ 5185 / 1000 :=
  UpperTwelveNumerics.callCost_tsum_le

example : wrongSideConstant < 401 / 1000 :=
  UpperTwelveNumerics.wrongSideConstant_lt

example : ∀ (B : ℝ), 4 ≤ B → B / (2 : ℝ) ^ BlindUpper.budgetLevel B < 8 :=
  UpperTwelveNumerics.dyadic_ratio_lt
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
        raise ValueError("Duplicate upper-twelve-numerics declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-twelve-numerics target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed upper-twelve-numerics specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open Finset ThresholdHC ThresholdHC.Tier6 ThresholdHC.UpperTwelveNumerics",
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
    print(f"All {len(TARGETS)} upper-twelve-numerics targets are certified")


if __name__ == "__main__":
    main()
