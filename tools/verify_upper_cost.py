"""Audit the upper constant 19 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 19 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 19 times the
modulus. The family is the budget mixture of `UpperMixture`. What changes is
the bound on the padded cost of one call: summed over the level differences
j = l - k, the checks of the early-stopping classifiers follow one dyadic grid
per threshold scale 1 + j*log 2, and offset bounds on those grids give 11/2 in
place of 273/25. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose two statements use only the original
   experiment, budget, risk and modulus definitions;
3. restates the two targets and eleven component theorems with their types
   written out, so a changed statement cannot pass under an old name;
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

PREFIX = "ThresholdHC.UpperCost."
SOURCES = LEAN / "ThresholdHC/UpperCost"
MODULES = ("Specification", "Offset", "Grid", "LevelSum", "Moments", "Batch", "Full")
SPEC_HASH = "240da188e88311f8d4537c16712c8d892ebd9a8db0e0cd756865e6f69add4b35"
TARGETS = {
    "blind_upper_19": "BlindUpper19Statement",
    "minimax_upper_19": "MinimaxUpper19Statement",
}
COMPONENTS = (
    "offset_le_first", "offset_le_rest", "grid_sum_le", "survivalBound_eq_grid",
    "cost_constant_le", "padded_levelSum_le", "paddedWorkMoment_le", "paddedCutoff_work_upper",
    "cutoffBatch_mse", "budgetMixture_risk_of_batch", "budgetMixture_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (19*modulus μ (1/Real.sqrt B)) :=
  UpperCost.blind_upper_19

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (19*modulus μ (1/Real.sqrt B)) :=
  UpperCost.minimax_upper_19

example : ∀ (s : ℝ), 1 ≤ s → s ≤ 2 → ∀ {v : ℝ}, (169 / 100 : ℝ) ≤ v → ∀ (I : ℕ),
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ Finset.range I,
      Real.sqrt (2 ^ i * s) * Real.exp (-2 * v * (Real.sqrt (2 ^ i * s) - 1) ^ 2) ≤
      (89 / 20 : ℝ) :=
  @UpperCost.offset_le_first

example : ∀ (s : ℝ), 1 ≤ s → s ≤ 2 → ∀ {v : ℝ}, (119 / 50 : ℝ) ≤ v → ∀ (I : ℕ),
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ Finset.range I,
      Real.sqrt (2 ^ i * s) * Real.exp (-2 * v * (Real.sqrt (2 ^ i * s) - 1) ^ 2) ≤
      (17 / 4 : ℝ) :=
  @UpperCost.offset_le_rest

example : ∀ {v d C : ℝ}, 1 ≤ v → 0 < d → d ^ 2 < v →
    (∀ s, 1 ≤ s → s ≤ 2 → ∀ I : ℕ, (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ Finset.range I,
      Real.sqrt (2 ^ i * s) * Real.exp (-2 * v * (Real.sqrt (2 ^ i * s) - 1) ^ 2) ≤ C) →
    ∀ (K : ℕ), ∑ k ∈ Finset.range K, Real.sqrt (Uniform713.cap k * d ^ 2) *
        (if v ≤ Uniform713.cap k * d ^ 2 then
          Real.exp (-2 * (Real.sqrt (Uniform713.cap k * d ^ 2) - Real.sqrt v) ^ 2) else 1) +
      d * (1 + Real.sqrt 2) ≤ Real.sqrt v * C :=
  @UpperCost.grid_sum_le

example : ∀ (k J : ℕ) {d : ℝ}, 0 < d →
    (if Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap (k + J)) ≤ d then
      Real.exp (-2 * Uniform713.cap k *
        (d - Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap (k + J))) ^ 2) else 1) =
      (if 1 + J * Real.log 2 ≤ Uniform713.cap k * d ^ 2 then
        Real.exp (-2 * (Real.sqrt (Uniform713.cap k * d ^ 2) - Real.sqrt (1 + J * Real.log 2)) ^ 2)
        else 1) :=
  @UpperCost.survivalBound_eq_grid

example : ∀ (L : ℕ), ∑ j ∈ Finset.range L, (1 - rLevel) * rLevel ^ (j + 1) *
      (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) * (if j = 0 then 89 / 20 else 17 / 4)) ≤
      11 / 2 :=
  UpperCost.cost_constant_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (w : ℕ → ℝ),
    (∀ l ≤ L, w l ≤ 1 + ∑ k ∈ Finset.range l, Uniform713.cap k *
      (if Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l) ≤ d then
        Real.exp (-2 * Uniform713.cap k *
          (d - Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l)) ^ 2) else 1)) →
    ∑ l ∈ Finset.range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (11 / 2) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ :=
  @UpperCost.padded_levelSum_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    workMomentK 1 1 L d S + rLevel ^ (L + 1) ≤ (11/2) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ :=
  UpperCost.paddedWorkMoment_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫ z, (BlindUpper.paddedCutoffCost L z : ℝ) ∂BlindUpper.callMeasure μ q) ≤
      (11/2)*∫ d, BlindUpper.callScale L d ∂μ :=
  @UpperCost.paddedCutoff_work_upper

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((401/5)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) :=
  @UpperCost.cutoffBatch_mse

example : ∀ {K c : ℝ}, 0 ≤ K → 1 ≤ c → (9/2) * K ≤ c ^ 2 →
    (∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
      squaredRisk (experimentLaw μ (BlindUpper.batchEstimator L) q)
          (populationOutput (BlindUpper.batchEstimator L)) (signMean μ q.val) ≤
        ENNReal.ofReal (K * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2)) →
    ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (c * modulus μ (1 / Real.sqrt B)) :=
  @UpperCost.budgetMixture_risk_of_batch

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (19 * modulus μ (1 / Real.sqrt B)) :=
  @UpperCost.budgetMixture_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-cost module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperCost/{name}.lean")
        roots.extend(public_names(source, f"UpperCost/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-cost declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-cost target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-cost statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperCost.{statement} := UpperCost.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperCost\.{re.escape(name)}\n", EXACT)) != 1:
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
    print("Both upper-cost target statements are certified")


if __name__ == "__main__":
    main()
