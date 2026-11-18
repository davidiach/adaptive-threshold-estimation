"""Audit the upper constant 36 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 36 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 36 times the
modulus. The family is the distribution-blind estimator of `BlindUpper`. The
proof sharpens the call second moment: two consecutive early-stopping
classifiers disagree with probability at most (113/100)/(cap*d^2)^2, keeping
5*errorPrefactor = (25/3)*exp(-2) in place of 3, and the level sum of the
second moment is at most 72/5 in place of 23. The call cost 248/25 is that of
`UpperWork` and the budget factor 17/6 that of `UpperConstant`. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose two statements use only the original
   experiment, budget, risk and modulus definitions;
3. restates the two targets and eight component theorems with their types
   written out, the error prefactor unfolded, so a changed statement cannot
   pass under an old name;
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

PREFIX = "ThresholdHC.UpperMoment."
SOURCES = LEAN / "ThresholdHC/UpperMoment"
MODULES = ("Specification", "Disagreement", "LevelSum", "Moments", "Batch", "Full")
SPEC_HASH = "a82b748ceaff3b70cac46c989a23251b9b59ff3d5106fa377e750c0b473f443f"
TARGETS = {
    "blind_upper_36": "BlindUpper36Statement",
    "minimax_upper_36": "MinimaxUpper36Statement",
}
COMPONENTS = (
    "errorPair_le", "increment_secondMoment_positive", "increment_secondMoment_negative",
    "secondMoment_levelSum_le", "secondMomentK_le", "cutoffBatch_mse", "batch_maximalRMSRisk_le",
    "budgetEstimator_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (36*modulus μ (1/Real.sqrt B)) :=
  UpperMoment.blind_upper_36

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (36*modulus μ (1/Real.sqrt B)) :=
  UpperMoment.minimax_upper_36

example : ∀ (L : ℕ) (d : ℝ), 0 < d →
    (5 / 3) * Real.exp (-2) / (Uniform713.cap (L + 1) * d ^ 2) ^ 2 +
        (5 / 3) * Real.exp (-2) / (Uniform713.cap L * d ^ 2) ^ 2 ≤
      (113 / 100) / (Uniform713.cap (L + 1) * d ^ 2) ^ 2 :=
  @UpperMoment.errorPair_le

example : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → Ω → ℝ} (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 / 2 →
    Uniform713.HasMeanTails μ m (1 / 2 + d) →
    (∫ ω, (Uniform713.increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 ((113 / 100) / (Uniform713.cap L * d ^ 2) ^ 2) :=
  @UpperMoment.increment_secondMoment_positive

example : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ → Ω → ℝ} (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 / 2 →
    Uniform713.HasMeanTails μ m (1 / 2 - d) →
    (∫ ω, (Uniform713.increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 ((113 / 100) / (Uniform713.cap L * d ^ 2) ^ 2) :=
  @UpperMoment.increment_secondMoment_negative

example : ∀ (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 / 2 → ∀ (e : ℕ → ℝ),
    (∀ l ≤ L, e l ≤ min 1 ((113 / 100) / (Uniform713.cap l * d ^ 2) ^ 2)) →
    ∑ l ∈ Finset.range (L + 1), e l / pLevel l ≤
      (72 / 5) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ :=
  UpperMoment.secondMoment_levelSum_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    secondMomentK 1 1 L d S ≤ (72/5) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ :=
  UpperMoment.secondMomentK_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((19781/125)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) :=
  @UpperMoment.cutoffBatch_mse

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (BlindUpper.batchEstimator L) ≤
      ENNReal.ofReal ((63/5)*modulus μ (1/Real.sqrt ((2 : ℝ)^L))) :=
  @UpperMoment.batch_maximalRMSRisk_le

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (BlindUpper.budgetEstimator B) ≤
      ENNReal.ofReal (36*modulus μ (1/Real.sqrt B)) :=
  @UpperMoment.budgetEstimator_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-moment module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperMoment/{name}.lean")
        roots.extend(public_names(source, f"UpperMoment/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-moment declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-moment target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-moment statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperMoment.{statement} := UpperMoment.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperMoment\.{re.escape(name)}\n", EXACT)) != 1:
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
    print("Both upper-moment target statements are certified")


if __name__ == "__main__":
    main()
