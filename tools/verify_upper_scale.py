"""Audit the upper constant 12 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 12 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 12 times the
modulus. Two steps give 12 in place of 13:

* `UpperCallCost` bounds the padded call cost by 26/5 in place of 11/2. The
  grid of level difference j + 1 has offset bound 399/100 for j >= 2, and
  the weighted sum of the offsets is bounded with the square root of each of
  the first eight threshold scales.
* `UpperScale` calibrates the batch at the scale B/4, which need not be a power
  of two. The batch machine of `BlindUpper`, run on a seed whose uniform marks
  are multiplied by t >= 1, realizes the calibration at scale t*2^L with the
  same calls, so the family uses the whole budget without the two-level
  mixture, and the mean-square error is at most 4*(t + 169/5) <= 716/5 times
  the squared modulus.

The audit

1. requires the two directories to hold exactly the registered modules and
   scans each for proof escapes;
2. pins the specification, whose two statements use only the original
   experiment, budget, risk and modulus definitions;
3. restates the two targets and twelve component theorems with their types
   written out, so a changed statement cannot pass under an old name;
4. reports the transitive axioms of every public declaration in the two
   directories.

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

GROUPS = {
    "UpperCallCost": ("Offset", "LevelSum", "Moments", "Batch"),
    "UpperScale": ("Specification", "Seed", "Batch", "Full"),
}
SOURCES = {group: LEAN / f"ThresholdHC/{group}" for group in GROUPS}
SPEC = SOURCES["UpperScale"] / "Specification.lean"
SPEC_HASH = "77bc40d6104566ae8fdf23d00796ed4a08d460a8020ce96da7e1cdc4277cf418"
TARGETS = {
    "UpperScale.blind_upper_12": "UpperScale.BlindUpper12Statement",
    "UpperScale.minimax_upper_12": "UpperScale.MinimaxUpper12Statement",
}
COMPONENTS = (
    "UpperCallCost.offset_le_far", "UpperCallCost.callCost_constant_le",
    "UpperCallCost.padded_levelSum_le", "UpperCallCost.padded_regime_le",
    "UpperCallCost.paddedWorkMoment_le", "UpperCallCost.paddedCutoff_work_upper",
    "UpperScale.callMark_scale", "UpperScale.scaled_uniformBudget",
    "UpperScale.scaled_squaredRisk_eq", "UpperScale.call_variance_cost_le",
    "UpperScale.scaledBatch_mse", "UpperScale.scaledFamily_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (12*modulus μ (1/Real.sqrt B)) :=
  UpperScale.blind_upper_12

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (12*modulus μ (1/Real.sqrt B)) :=
  UpperScale.minimax_upper_12

example : ∀ (s : ℝ), 1 ≤ s → s ≤ 2 → ∀ {v : ℝ}, (307 / 100 : ℝ) ≤ v → ∀ (I : ℕ),
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ Finset.range I,
      Real.sqrt (2 ^ i * s) * Real.exp (-2 * v * (Real.sqrt (2 ^ i * s) - 1) ^ 2) ≤
      (399 / 100 : ℝ) :=
  @UpperCallCost.offset_le_far

example : ∀ (L : ℕ), ∑ j ∈ Finset.range L, (1 - rLevel) * rLevel ^ (j + 1) *
    (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) *
      (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100)) ≤ 26 / 5 :=
  UpperCallCost.callCost_constant_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (w : ℕ → ℝ),
    (∀ l ≤ L, w l ≤ 1 + ∑ k ∈ Finset.range l, Uniform713.cap k *
      (if Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l) ≤ d then
        Real.exp (-2 * Uniform713.cap k *
          (d - Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l)) ^ 2) else 1)) →
    ∑ l ∈ Finset.range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (26 / 5) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ :=
  @UpperCallCost.padded_levelSum_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (w : ℕ → ℝ),
    (∀ l ≤ L, w l ≤ 1 + ∑ k ∈ Finset.range l, Uniform713.cap k *
      (if Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l) ≤ d then
        Real.exp (-2 * Uniform713.cap k *
          (d - Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l)) ^ 2) else 1)) →
    ∑ l ∈ Finset.range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (26 / 5) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ -
        (21 / 5) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  @UpperCallCost.padded_regime_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    workMomentK 1 1 L d S + rLevel ^ (L + 1) ≤ (26/5) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ -
      (21/5) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  UpperCallCost.paddedWorkMoment_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫ z, (BlindUpper.paddedCutoffCost L z : ℝ) ∂BlindUpper.callMeasure μ q) ≤
      (26/5)*∫ d, BlindUpper.callScale L d ∂μ -
        (21/5)*∫ d, UpperDisagreement.gapRegime L d ∂μ :=
  @UpperCallCost.paddedCutoff_work_upper

example : ∀ (L : ℕ) (t : ℝ) (x : ℕ × (ℕ → Bool)) (u : ℝ),
    BlindUpper.callMark (BlindUpper.paddedMark L) (x, max t 1 * u) =
      BlindUpper.callMark (UpperScale.scaledMark L t) (x, u) :=
  UpperScale.callMark_scale

example : ∀ (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ],
    UniformBudget μ (UpperScale.scaledEstimator L t) (4 * (max t 1 * (2 : ℝ) ^ L)) :=
  @UpperScale.scaled_uniformBudget

example : ∀ (L : ℕ) (t : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ),
    squaredRisk (experimentLaw μ (UpperScale.scaledEstimator L t) q)
        (populationOutput (UpperScale.scaledEstimator L t)) a =
      ∫⁻ z, ENNReal.ofReal ((BlindUpper.calibrationOutput (UpperScale.scaledMark L t)
        (BlindUpper.cutoffValue L) z - a) ^ 2) ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q) :=
  @UpperScale.scaled_squaredRisk_eq

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    ProbabilityTheory.variance (BlindUpper.cutoffValue L) (BlindUpper.callMeasure μ q) *
        (∫ z, (BlindUpper.paddedCutoffCost L z : ℝ) ∂BlindUpper.callMeasure μ q) ≤
      (169/5) * (∫ d, BlindUpper.callScale L d ∂μ) ^ 2 :=
  @UpperScale.call_variance_cost_le

example : ∀ (L : ℕ) {t : ℝ}, 1 ≤ t → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.calibrationOutput (UpperScale.scaledMark L t)
        (BlindUpper.cutoffValue L) z - signMean μ q.val) ^ 2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((1 + (169/5) / t) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) :=
  @UpperScale.scaledBatch_mse

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (UpperScale.scaledFamily B) ≤
      ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B)) :=
  @UpperScale.scaledFamily_maximalRMSRisk
"""


def modules() -> list[str]:
    return [f"{group}.{name}" for group, names in GROUPS.items() for name in names]


def declared_roots() -> set[str]:
    roots: list[str] = []
    for group, names in GROUPS.items():
        found = {p.stem for p in SOURCES[group].glob("*.lean")}
        if found != set(names) or len(names) != len(set(names)):
            raise ValueError(f"Unregistered or missing {group} module")
        for name in names:
            source = strip_comments((SOURCES[group] / f"{name}.lean").read_text(encoding="utf-8"))
            if FORBIDDEN.search(source):
                raise ValueError(f"Forbidden proof escape in {group}/{name}.lean")
            names_here = public_names(source, f"{group}/{name}.lean")
            if any(not root.startswith(f"ThresholdHC.{group}.") for root in names_here):
                raise ValueError(f"{group}/{name}.lean must declare in ThresholdHC.{group}")
            roots.extend(names_here)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-scale declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-scale target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed upper-scale statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
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
    print("Both upper-scale target statements are certified")


if __name__ == "__main__":
    main()
