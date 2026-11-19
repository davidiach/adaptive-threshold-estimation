"""Audit the upper constant 15 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 15 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 15 times the
modulus. The family is the budget mixture of `UpperMixture`, with the padded
call cost of `UpperCost` and the regime term of `UpperDisagreement`. What
changes is the call second moment below the cap scale: the majority votes
after n and 2n flips change sign with probability at most one half, because
the two halves of the flips are independent with the same law, so
consecutive classifiers past the first level disagree with probability at
most one half plus the early-stop bound of the smaller one. The audit

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

PREFIX = "ThresholdHC.UpperSign."
SOURCES = LEAN / "ThresholdHC/UpperSign"
MODULES = ("Specification", "SignChange", "EarlyStop", "Drift", "Offset", "Grid", "Increment",
           "LevelSum", "Moments", "Batch", "Full")
SPEC_HASH = "cb8efc858820f6f4f8fe410e364f53cab821695b3d246f7e934dba7d367d1138"
TARGETS = {
    "blind_upper_15": "BlindUpper15Statement",
    "minimax_upper_15": "MinimaxUpper15Statement",
}
COMPONENTS = (
    "count_signChange_le", "disagree_tape_le", "drift_step_le", "below_coef_le",
    "sign_offset_le", "sign_grid_le", "sign_increment_le", "sign_levelSum_le",
    "secondMomentK_le", "cutoffBatch_mse", "budgetMixture_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (15*modulus μ (1/Real.sqrt B)) :=
  UpperSign.blind_upper_15

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (15*modulus μ (1/Real.sqrt B)) :=
  UpperSign.minimax_upper_15

example : ∀ (m : ℕ) (p : unitInterval),
    (Tier2.tapeMeasure p).real {ω | (m < UpperSign.successes 0 (2 * m) ω ∧
        UpperSign.successes (2 * m) (2 * m) ω < m) ∨
      (UpperSign.successes 0 (2 * m) ω ≤ m ∧ m < UpperSign.successes (2 * m) (2 * m) ω)} ≤ 1 / 2 :=
  UpperSign.count_signChange_le

example : ∀ (L : ℕ), 1 ≤ L → ∀ (p : unitInterval) {d : ℝ},
    (Tier2.tapeMeasure p).real {ω | ∃ k < L, Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L) <
      |Uniform713.dyadicMean Tier2.observations k ω - 1/2|} ≤ UpperSign.earlyBound L d →
    (Tier2.tapeMeasure p).real {ω |
      Tier2.Model.decision (fun k => Uniform713.dyadicMean Tier2.observations k ω) (L + 1) ≠
        Tier2.Model.decision (fun k => Uniform713.dyadicMean Tier2.observations k ω) L} ≤
      1 / 2 + UpperSign.earlyBound L d :=
  @UpperSign.disagree_tape_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → ∀ (i : ℕ),
    Uniform713.cap L * d ^ 2 ≤ 3 / 2 ^ (i + 3) →
    ∑ k ∈ Finset.range L, UpperSign.driftBound L k d ≤ UpperSign.stepE i :=
  @UpperSign.drift_step_le

example : ∀ (n : ℕ), ∑ i ∈ Finset.range n, rLevel ^ (i + 1) * (1 / 2 + UpperSign.stepE i) +
    rLevel ^ (n + 1) + rLevel ^ (n + 2) ≤ 1613 / 1000 :=
  UpperSign.below_coef_le

example : ∀ (s : ℝ), 3 / 4 ≤ s → s ≤ 3 / 2 → ∀ (I : ℕ),
    (1613 / 1000 : ℝ) * Real.sqrt s + ∑ i ∈ Finset.range I,
      Real.sqrt (2 ^ i * s) * (Real.exp (-2 * (2 ^ i * s)) + Real.exp (-(2 ^ i * s))) ≤
      (247 / 100 : ℝ) :=
  UpperSign.sign_offset_le

example : ∀ {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (K : ℕ),
    ∑ l ∈ Finset.range K, Real.sqrt (Uniform713.cap l * d ^ 2) * UpperSign.signWeight l d ≤
      247 / 100 :=
  @UpperSign.sign_grid_le

example : ∀ (L : ℕ) (p : unitInterval) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (s : ℝ),
    (∀ L, (Tier2.tapeMeasure p).real {ω | Tier2.Model.decision
      (fun k => Uniform713.dyadicMean Tier2.observations k ω) L ≠ s} ≤
        Tier2.Model.errorUnionBound L d) →
    (∀ L, (Tier2.tapeMeasure p).real {ω | ∃ k < L,
      Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L) <
        |Uniform713.dyadicMean Tier2.observations k ω - 1/2|} ≤ UpperSign.earlyBound L d) →
    (∫ ω, (Uniform713.increment (fun k => Tier2.Model.decision
      (fun j => Uniform713.dyadicMean Tier2.observations j ω) k) L) ^ 2 ∂Tier2.tapeMeasure p) ≤
      min 1 (UpperSign.signWeight L d + UpperDisagreement.stopError L d +
        UpperDisagreement.stopError (L - 1) d) :=
  @UpperSign.sign_increment_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (e : ℕ → ℝ),
    (∀ l ≤ L, e l ≤ min 1 (UpperSign.signWeight l d + UpperDisagreement.stopError l d +
      UpperDisagreement.stopError (l - 1) d)) →
    ∑ l ∈ Finset.range (L + 1), e l / pLevel l ≤
      (89 / 10) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ +
        (69 / 25) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  @UpperSign.sign_levelSum_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    secondMomentK 1 1 L d S ≤ (89/10) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ +
      (69/25) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  UpperSign.secondMomentK_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((999/20)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) :=
  @UpperSign.cutoffBatch_mse

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (15 * modulus μ (1 / Real.sqrt B)) :=
  @UpperSign.budgetMixture_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-sign module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperSign/{name}.lean")
        roots.extend(public_names(source, f"UpperSign/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-sign declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-sign target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-sign statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperSign.{statement} := UpperSign.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperSign\.{re.escape(name)}\n", EXACT)) != 1:
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
    print("Both upper-sign target statements are certified")


if __name__ == "__main__":
    main()
