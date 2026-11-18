"""Audit the upper constant 17 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 17 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 17 times the
modulus. The family is the budget mixture of `UpperMixture`, and the padded
call cost is that of `UpperCost`. What changes is the call second moment:
consecutive classifiers disagree only if one errs, and each error is bounded
by its union bound, whose cap terms are summed along the dyadic grid of
levels and whose early-stopping terms are summed by a telescoping bound. A
regime term, carried through the second moment and the padded cost, cancels
in their product. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose two statements use only the original
   experiment, budget, risk and modulus definitions;
3. restates the two targets and twelve component theorems with their types
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

PREFIX = "ThresholdHC.UpperDisagreement."
SOURCES = LEAN / "ThresholdHC/UpperDisagreement"
MODULES = ("Specification", "CapOffset", "CapGrid", "ErrorSum", "Increment", "LevelSum",
           "Moments", "Batch", "Full")
SPEC_HASH = "b3f161268595fcc52125a581c0b280cdcb084798e8fb472248aba93450b7bfcc"
TARGETS = {
    "blind_upper_17": "BlindUpper17Statement",
    "minimax_upper_17": "MinimaxUpper17Statement",
}
COMPONENTS = (
    "cap_offset_le", "cap_grid_le", "grid_exp_le", "stopError_levelSum_le",
    "increment_sq_positive", "increment_sq_negative", "disagreement_levelSum_le",
    "padded_regime_le", "secondMomentK_le", "paddedWorkMoment_le", "cutoffBatch_mse",
    "budgetMixture_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (17*modulus μ (1/Real.sqrt B)) :=
  UpperDisagreement.blind_upper_17

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (17*modulus μ (1/Real.sqrt B)) :=
  UpperDisagreement.minimax_upper_17

example : ∀ (s : ℝ), 12 / 25 ≤ s → s ≤ 24 / 25 → ∀ (I : ℕ),
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ Finset.range I,
      Real.sqrt (2 ^ i * s) * (Real.exp (-2 * (2 ^ i * s)) + Real.exp (-(2 ^ i * s))) ≤
      (321 / 100 : ℝ) :=
  UpperDisagreement.cap_offset_le

example : ∀ {d : ℝ}, 0 < d → d ^ 2 < 12 / 25 → ∀ (K : ℕ),
    ∑ l ∈ Finset.range K, Real.sqrt (Uniform713.cap l * d ^ 2) *
      (if 12 / 25 ≤ Uniform713.cap l * d ^ 2 then
        Real.exp (-2 * (Uniform713.cap l * d ^ 2)) + Real.exp (-(Uniform713.cap l * d ^ 2))
        else 1) ≤ 321 / 100 :=
  @UpperDisagreement.cap_grid_le

example : ∀ {c d : ℝ}, 0 < c → 0 < d → ∀ (K : ℕ),
    ∑ k ∈ Finset.range K, (Real.sqrt 2 ^ k * d) * Real.exp (-c * (Real.sqrt 2 ^ k * d)) ≤
      (2 + Real.sqrt 2) / c :=
  @UpperDisagreement.grid_exp_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d →
    d * ∑ l ∈ Finset.range (L + 1),
      ((∑ k ∈ Finset.range l, Real.exp (-2 * Uniform713.cap k *
          (d + Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l)) ^ 2)) +
        (∑ k ∈ Finset.range (l - 1), Real.exp (-2 * Uniform713.cap k *
          (d + Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap (l - 1))) ^ 2))) /
        pLevel l ≤ 41 / 100 :=
  @UpperDisagreement.stopError_levelSum_le

example : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → Ω → ℝ} (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 →
    Uniform713.HasMeanTails μ m (1 / 2 + d) →
    (∫ ω, (Uniform713.increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 (UpperDisagreement.levelBound L d) :=
  @UpperDisagreement.increment_sq_positive

example : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → Ω → ℝ} (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 →
    Uniform713.HasMeanTails μ m (1 / 2 - d) →
    (∫ ω, (Uniform713.increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 (UpperDisagreement.levelBound L d) :=
  @UpperDisagreement.increment_sq_negative

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (e : ℕ → ℝ),
    (∀ l ≤ L, e l ≤ min 1 (UpperDisagreement.levelBound l d)) →
    ∑ l ∈ Finset.range (L + 1), e l / pLevel l ≤
      (57 / 5) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ +
        (13 / 50) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  @UpperDisagreement.disagreement_levelSum_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (w : ℕ → ℝ),
    (∀ l ≤ L, w l ≤ 1 + ∑ k ∈ Finset.range l, Uniform713.cap k *
      (if Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l) ≤ d then
        Real.exp (-2 * Uniform713.cap k *
          (d - Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap l)) ^ 2) else 1)) →
    ∑ l ∈ Finset.range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (11 / 2) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ -
        (9 / 2) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  @UpperDisagreement.padded_regime_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    secondMomentK 1 1 L d S ≤ (57/5) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ +
      (13/50) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  UpperDisagreement.secondMomentK_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    workMomentK 1 1 L d S + rLevel ^ (L + 1) ≤ (11/2) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ -
      (9/2) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  UpperDisagreement.paddedWorkMoment_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((637/10)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) :=
  @UpperDisagreement.cutoffBatch_mse

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (17 * modulus μ (1 / Real.sqrt B)) :=
  @UpperDisagreement.budgetMixture_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-disagreement module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperDisagreement/{name}.lean")
        roots.extend(public_names(source, f"UpperDisagreement/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-disagreement declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-disagreement target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-disagreement statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperDisagreement.{statement} := UpperDisagreement.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperDisagreement\.{re.escape(name)}\n", EXACT)) != 1:
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
    print("Both upper-disagreement target statements are certified")


if __name__ == "__main__":
    main()
