"""Audit the bracket for the RMS lower coefficient at budgets of at least 25.

For every gap law and every budget at least 25, minimax RMS risk is at least
0.175198 times the modulus, in the ordinary experiment and under both magnitude
oracles; at budgets of at least 100 the coefficient is 0.17807955. At the gap
one fifth and the budget 25 an adaptive policy with at most 25 flips on every
path has worst-case RMS risk at most 0.186752, so no coefficient above 0.186752
holds at every budget of at least 25. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose four statements use only the original
   experiment, risk and modulus definitions;
3. restates the four targets and twenty component theorems with their types
   written out, so a changed statement cannot pass under an old name;
4. reports the transitive axioms of every public declaration in the directory.

The components include two intermediate results that the targets improve:
the coefficients 0.17356166 (B >= 25) and 0.17623782 (B >= 100) from three
biases, and the upper 0.195454 from twenty-five fresh flips. They are restated
because the targets' proofs build on the same modules.

Helper lemmas are private and are covered by the whole-project audit
(`verify_project_axioms.py`). With --replay the registered modules also go
through the toolchain's independent kernel checker, which re-evaluates the
integer certificates of the five-bias test and the pilot policy.

The modules are copies of the research files of
`research/2026-11-17-rms-constants` with library imports and LF line endings.
The statements were written after the proofs, from that research package;
they are pinned from this audit onward.
"""
from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

PREFIX = "ThresholdHC.LargeBudgetRMS."
SOURCES = LEAN / "ThresholdHC/LargeBudgetRMS"
# Dependency order; the research file names are kept.
MODULES = (
    "Specification",
    "LargeBudgetFresh", "LargeBudgetBinomial", "LargeBudgetInformation", "LargeBudgetTest",
    "LargeBudgetTable", "LargeBudgetTranscript", "LargeBudgetPrice", "LargeBudgetRisk",
    "LargeBudgetPopulation", "LargeBudgetBounds", "LargeBudgetWitness",
    "RevisitPolynomial", "RevisitKernel", "RevisitPolicy",
    "MultiBiasData", "MultiBiasCertificate", "MultiBiasPrice", "MultiBiasPrefix",
    "MultiBiasPopulation", "MultiBiasBounds",
    "PilotPolicy", "PilotTable", "PilotExperiment", "PilotPolynomial", "PilotCertificate",
    "PilotWitness", "Full",
)
SPEC_HASH = "35d347e6fdf9148118f2ff417b1786294a877375ae65fc0b63f1ef232f6500cc"
TARGETS = {
    "bracket_lower": "BracketLowerStatement",
    "hundred_lower": "HundredLowerStatement",
    "fifth_gap_upper": "FifthGapUpperStatement",
    "bracket_upper": "BracketUpperStatement",
}
# Relative to ThresholdHC.SharpRMS, the namespace of the research proofs.
COMPONENT_PREFIX = "ThresholdHC.SharpRMS."
COMPONENTS = (
    "LargeBudget.adaptive_reverse_cost", "LargeBudget.log_tests", "LargeBudget.logarithmic_lower",
    "LargeBudget.lower_25", "LargeBudget.lower_100", "LargeBudget.twenty_five_budget",
    "LargeBudget.twenty_five_squared_risk", "LargeBudget.upper_25", "LargeBudget.coefficient_upper",
    "MultiBias.scalar_test", "MultiBias.lower_of_price", "MultiBias.lower_curve",
    "MultiBias.lower_25", "MultiBias.lower_100",
    "Pilot.pilot_cap", "Pilot.pilot_budget", "Pilot.pilot_squared_risk", "Pilot.pilot_worst_squared",
    "Pilot.pilot_upper_25", "Pilot.pilot_coefficient_upper",
)
# One further example evaluates the pilot's exact worst squared risk.
EXACT_COUNT = len(TARGETS) + len(COMPONENTS) + 1

TARGETS_EXACT = """
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (175198/1000000 : ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (175198/1000000 : ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (175198/1000000 : ℝ)) ≤ selectedMinimaxRisk μ B :=
  LargeBudgetRMS.bracket_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 100 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (17807955/100000000 : ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (17807955/100000000 : ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (17807955/100000000 : ℝ)) ≤ selectedMinimaxRisk μ B :=
  LargeBudgetRMS.hundred_lower

example : minimaxRisk (Measure.dirac (⟨1/5, by norm_num⟩ : Gap)) 25 ≤
    ENNReal.ofReal (186752/1000000 : ℝ) :=
  LargeBudgetRMS.fifth_gap_upper

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B) → c ≤ 186752/1000000 :=
  LargeBudgetRMS.bracket_upper
"""

# Each section opens the one research namespace whose definitions its
# statements name, as the research audit files did.
COMPONENTS_EXACT = """
section
open ThresholdHC.SharpRMS.LargeBudget

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s t : ℝ), 0<s → s<1 → t^2≤2/3 →
    let Q := fun a : ℝ => creationLaw (n:=n) pol (fun _ => s/2) (fun _ => (1+a)/2)
    pairedCost (Q 0) (Q t) (Q (-t)) ≤ -log (1-t^2*s^2)*∑ w, Q 0 w*workOf w :=
  @LargeBudget.adaptive_reverse_cost

example : ∀ x : ℝ, |x|≤1 → 27401/10000 ≤
    log (1/8+29/4*(x-29/40)^2)+log (1/8+29/4*(x- -(29/40))^2)+11774928000/2595112129*x^2 :=
  LargeBudget.log_tests

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B r : ℝ), 25≤B → 0<r →
    4*(11774928000/2595112129+2*(29/4))*r^2-log (1-4*(29/40)^2/B)*B ≤ 27401/10000+2*(1-1/8) →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(r:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(r:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(r:ℝ)) ≤ selectedMinimaxRisk μ B :=
  @LargeBudget.logarithmic_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17356166/100000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17356166/100000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17356166/100000000:ℝ)) ≤ selectedMinimaxRisk μ B :=
  @LargeBudget.lower_25

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 100≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17623782/100000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17623782/100000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17623782/100000000:ℝ)) ≤ selectedMinimaxRisk μ B :=
  @LargeBudget.lower_100

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ twentyFiveFlips 25 :=
  @LargeBudget.twenty_five_budget

example : ∀ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) twentyFiveFlips q)
    (populationOutput twentyFiveFlips) (signMean (Measure.dirac fifthGap) q.val) ≤
    ENNReal.ofReal ((195454/1000000:ℝ)^2) :=
  LargeBudget.twenty_five_squared_risk

example : minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal (195454/1000000:ℝ) :=
  LargeBudget.upper_25

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) → c ≤ 195454/1000000 :=
  LargeBudget.coefficient_upper

end

section
open ThresholdHC.SharpRMS.MultiBias

example : ∀ x : ℝ, |x|≤1 →
    tilt*target-25*(∑ i, log (cut i)) ≤ tilt*x^2+∑ i, pair i x :=
  MultiBias.scalar_test

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B r : ℝ), 25≤B → 0<r →
    weightSum*(4*r^2-target)+price B≤price 25 →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*r) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*r) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*r) ≤ selectedMinimaxRisk μ B :=
  @MultiBias.lower_of_price

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ThresholdHC.SharpRMS.LargeBudget.lowerForAll μ B
      (Real.sqrt (4*(175198/1000000:ℝ)^2+(price 25-price B)/weightSum)/2) :=
  @MultiBias.lower_curve

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(175198/1000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(175198/1000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(175198/1000000:ℝ)) ≤ selectedMinimaxRisk μ B :=
  @MultiBias.lower_25

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 100≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17807955/100000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17807955/100000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17807955/100000000:ℝ)) ≤ selectedMinimaxRisk μ B :=
  @MultiBias.lower_100

end

section
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

example : HardBudget.PathwiseCap pilotEstimator 25 :=
  Pilot.pilot_cap

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ pilotEstimator 25 :=
  @Pilot.pilot_budget

example : ∀ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
    (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val) ≤
    ENNReal.ofReal ((186752/1000000:ℝ)^2) :=
  Pilot.pilot_squared_risk

example : (⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
    (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) =
    ENNReal.ofReal ((endpoint:ℝ) / 10^35) :=
  Pilot.pilot_worst_squared

example : ((endpoint:ℤ):ℝ) / 10^35 = 348763093753675683898541718818533/10^34 := by
  norm_num [endpoint]

example : minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal (186752/1000000:ℝ) :=
  Pilot.pilot_upper_25

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) → c ≤ 186752/1000000 :=
  Pilot.pilot_coefficient_upper

end
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing large-budget RMS module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in LargeBudgetRMS/{name}.lean")
        roots.extend(public_names(source, f"LargeBudgetRMS/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate large-budget RMS declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {COMPONENT_PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing large-budget RMS target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed large-budget RMS statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory Real",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6",
        "open ThresholdHC.OracleLower ThresholdHC.SharpRMS",
        *[f"example : LargeBudgetRMS.{statement} := LargeBudgetRMS.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        TARGETS_EXACT.strip("\n"),
        COMPONENTS_EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    exact = "\n" + TARGETS_EXACT + COMPONENTS_EXACT
    if exact.count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in [f"LargeBudgetRMS.{theorem}" for theorem in TARGETS] + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?{re.escape(name)}\n", exact)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return [PREFIX + name for name in MODULES]


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
        print(f"Replayed {len(MODULES)} modules through the independent kernel checker")
    print("All four large-budget RMS target statements are certified")


if __name__ == "__main__":
    main()
