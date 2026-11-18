"""Audit the upper constant 45 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 45 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 45 times the
modulus. The family is the distribution-blind estimator of `BlindUpper`. The
proof sharpens the per-level expected work of its early-stopping classifiers:
the survival probability at each check is bounded by Hoeffding's inequality at
the gap minus the stopping threshold, which gives at most
(49/10)*d^-2*(1 + log(cap*d^2)) flips per level in place of 17 times the work
envelope. Summed over levels, the call cost is at most 248/25 in place of 527/7.
The call second moment 23 and the budget factor 17/6 are those of
`UpperConstant`. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose two statements use only the original
   experiment, budget, risk and modulus definitions;
3. restates the two targets and nine component theorems with their types
   written out, the local definitions `bump` and `survivalBound` unfolded, so a
   changed statement cannot pass under an old name;
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

PREFIX = "ThresholdHC.UpperWork."
SOURCES = LEAN / "ThresholdHC/UpperWork"
MODULES = ("Specification", "Dyadic", "Survival", "LevelSum", "Moments", "Batch", "Full")
SPEC_HASH = "4da363450abf4dbc7be574b81a25c7d0fd2916e021827c27d686138cbc23c6eb"
TARGETS = {
    "blind_upper_45": "BlindUpper45Statement",
    "minimax_upper_45": "MinimaxUpper45Statement",
}
COMPONENTS = (
    "offset_sum_le", "survival_sum_le", "expected_work_positive", "expected_work_negative",
    "work_levelSum_le", "workMomentK_le", "cutoffBatch_mse", "batch_maximalRMSRisk_le",
    "budgetEstimator_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (45*modulus μ (1/Real.sqrt B)) :=
  UpperWork.blind_upper_45

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (45*modulus μ (1/Real.sqrt B)) :=
  UpperWork.minimax_upper_45

example : ∀ (s : ℝ), 1 < s → s ≤ 2 → ∀ (J : ℕ),
    s + ∑ j ∈ Finset.range J,
      (2 ^ j * s) * Real.exp (-2 * (Real.sqrt (2 ^ j * s) - 1) ^ 2) ≤ 49 / 10 :=
  UpperWork.offset_sum_le

example : ∀ (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 / 2 → 1 ≤ Uniform713.cap L * d ^ 2 →
    1 + ∑ k ∈ Finset.range L, Uniform713.cap k *
      (if Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L) ≤ d then
        Real.exp (-2 * Uniform713.cap k *
          (d - Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L)) ^ 2) else 1) ≤
      (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (Uniform713.cap L * d ^ 2)) :=
  @UpperWork.survival_sum_le

example : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → Ω → ℝ} (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 / 2 →
    Uniform713.HasMeanTails μ m (1 / 2 + d) → 1 ≤ Uniform713.cap L * d ^ 2 →
    (∫ ω, Tier2.Model.work (fun k => m k ω) L ∂μ) ≤
      (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (Uniform713.cap L * d ^ 2)) :=
  @UpperWork.expected_work_positive

example : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → Ω → ℝ} (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 / 2 →
    Uniform713.HasMeanTails μ m (1 / 2 - d) → 1 ≤ Uniform713.cap L * d ^ 2 →
    (∫ ω, Tier2.Model.work (fun k => m k ω) L ∂μ) ≤
      (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (Uniform713.cap L * d ^ 2)) :=
  @UpperWork.expected_work_negative

example : ∀ (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 / 2 → ∀ (w : ℕ → ℝ),
    (∀ l ≤ L, w l ≤ Uniform713.cap l) →
    (∀ l ≤ L, 1 ≤ Uniform713.cap l * d ^ 2 →
      w l ≤ (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (Uniform713.cap l * d ^ 2))) →
    ∑ l ∈ Finset.range (L + 1), pLevel l * w l ≤
      (248 / 25) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ :=
  UpperWork.work_levelSum_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    workMomentK 1 1 L d S ≤ (248/25) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ :=
  UpperWork.workMomentK_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((6304/25)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) :=
  @UpperWork.cutoffBatch_mse

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (BlindUpper.batchEstimator L) ≤
      ENNReal.ofReal ((397/25)*modulus μ (1/Real.sqrt ((2 : ℝ)^L))) :=
  @UpperWork.batch_maximalRMSRisk_le

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (BlindUpper.budgetEstimator B) ≤
      ENNReal.ofReal (45*modulus μ (1/Real.sqrt B)) :=
  @UpperWork.budgetEstimator_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-work module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperWork/{name}.lean")
        roots.extend(public_names(source, f"UpperWork/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-work declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-work target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-work statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperWork.{statement} := UpperWork.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperWork\.{re.escape(name)}\n", EXACT)) != 1:
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
    print("Both upper-work target statements are certified")


if __name__ == "__main__":
    main()
