"""Audit the improved upper constant 119 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 119 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 119 times the
modulus. The family is the distribution-blind estimator of `BlindUpper`. Its
call moments are bounded with the level sums that the existing library already
proves (23 for the second moment and 527/7 for the cost) in place of the frozen
targets 85 and 149, and the budget is compared with the factor 17/6 in place
of 4. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose two statements use only the original
   experiment, budget, risk and modulus definitions;
3. restates the two targets and five component theorems with their types
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

PREFIX = "ThresholdHC.UpperConstant."
SOURCES = LEAN / "ThresholdHC/UpperConstant"
MODULES = ("Specification", "Moments", "Batch", "Full")
SPEC_HASH = "eb0fb05a8860976b7b445bc4961e348a6358925ca98ffd1b42fd4206b04a953f"
TARGETS = {
    "blind_upper_119": "BlindUpper119Statement",
    "minimax_upper_119": "MinimaxUpper119Statement",
}
COMPONENTS = (
    "secondMomentK_le", "workMomentK_le", "cutoffBatch_mse", "batch_maximalRMSRisk_le",
    "budgetEstimator_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (119*modulus μ (1/Real.sqrt B)) :=
  UpperConstant.blind_upper_119

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (119*modulus μ (1/Real.sqrt B)) :=
  UpperConstant.minimax_upper_119

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    secondMomentK 1 1 L d S ≤ 23 * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ :=
  UpperConstant.secondMomentK_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    workMomentK 1 1 L d S ≤ (527/7) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ :=
  UpperConstant.workMomentK_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((12289/7)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) :=
  @UpperConstant.cutoffBatch_mse

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (BlindUpper.batchEstimator L) ≤
      ENNReal.ofReal (42*modulus μ (1/Real.sqrt ((2 : ℝ)^L))) :=
  @UpperConstant.batch_maximalRMSRisk_le

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (BlindUpper.budgetEstimator B) ≤
      ENNReal.ofReal (119*modulus μ (1/Real.sqrt B)) :=
  @UpperConstant.budgetEstimator_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-constant module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperConstant/{name}.lean")
        roots.extend(public_names(source, f"UpperConstant/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-constant declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-constant target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-constant statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperConstant.{statement} := UpperConstant.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperConstant\.{re.escape(name)}\n", EXACT)) != 1:
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
    print("Both upper-constant target statements are certified")


if __name__ == "__main__":
    main()
