"""Audit the upper constant 13 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 13 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 13 times the
modulus. The family is the budget mixture of `UpperMixture`, with the padded
call cost of `UpperCost` and the regime term of `UpperDisagreement`. What
changes is the call second moment below the cap scale: the majority votes
after n and 2n flips change sign with probability exactly a(1 - a) <= 1/4,
because the joint law of the two block counts is invariant under the swap,
so consecutive classifiers disagree with probability at most one quarter plus
the early-stop bound of the smaller one, at every level. The audit

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

PREFIX = "ThresholdHC.UpperQuarter."
SOURCES = LEAN / "ThresholdHC/UpperQuarter"
MODULES = ("Specification", "VoteChange", "EarlyStop", "Drift", "DriftTable", "Offset", "Grid",
           "Increment", "LevelSum", "Moments", "Batch", "Full")
SPEC_HASH = "7ce93e45a5d091092c141e1c05e5e41d7ded079e2fa3591ac81dd344659ede1c"
TARGETS = {
    "blind_upper_13": "BlindUpper13Statement",
    "minimax_upper_13": "MinimaxUpper13Statement",
}
COMPONENTS = (
    "count_voteChange_le", "disagree_tape_quarter", "band_step_le", "band_coef_le",
    "band_offset_le", "quarter_grid_le", "quarter_increment_le", "quarter_levelSum_le",
    "secondMomentK_le", "cutoffBatch_mse", "budgetMixture_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (13*modulus μ (1/Real.sqrt B)) :=
  UpperQuarter.blind_upper_13

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (13*modulus μ (1/Real.sqrt B)) :=
  UpperQuarter.minimax_upper_13

example : ∀ (n : ℕ) (p : unitInterval),
    (Tier2.tapeMeasure p).real {ω | (n < 2 * UpperSign.successes 0 n ω ∧
        UpperSign.successes 0 n ω + UpperSign.successes n n ω ≤ n) ∨
      (2 * UpperSign.successes 0 n ω ≤ n ∧
        n < UpperSign.successes 0 n ω + UpperSign.successes n n ω)} ≤ 1 / 4 :=
  UpperQuarter.count_voteChange_le

example : ∀ (L : ℕ) (p : unitInterval) {d : ℝ},
    (Tier2.tapeMeasure p).real {ω | ∃ k < L, Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L) <
      |Uniform713.dyadicMean Tier2.observations k ω - 1/2|} ≤ UpperSign.earlyBound L d →
    (Tier2.tapeMeasure p).real {ω |
      Tier2.Model.decision (fun k => Uniform713.dyadicMean Tier2.observations k ω) (L + 1) ≠
        Tier2.Model.decision (fun k => Uniform713.dyadicMean Tier2.observations k ω) L} ≤
      1 / 4 + UpperSign.earlyBound L d :=
  @UpperQuarter.disagree_tape_quarter

example : ∀ (k : ℕ), k < 4 → ∀ (L i : ℕ) {d : ℝ}, 0 < d →
    Uniform713.cap L * d ^ 2 ≤ UpperQuarter.bandTop k / 2 ^ (i + 2) →
    ∑ j ∈ Finset.range L, UpperSign.driftBound L j d ≤ UpperQuarter.bandStep k i :=
  @UpperQuarter.band_step_le

example : ∀ (k : ℕ), k < 4 → ∀ (n : ℕ),
    ∑ i ∈ Finset.range n, rLevel ^ (i + 1) * (1 / 4 + UpperQuarter.bandStep k i) +
      rLevel ^ (n + 1) ≤ UpperQuarter.bandCoef k :=
  @UpperQuarter.band_coef_le

example : ∀ (k : ℕ), k < 4 → ∀ (s : ℝ), UpperQuarter.bandBot k ≤ s → s ≤ UpperQuarter.bandTop k →
    ∀ (I : ℕ), UpperQuarter.bandCoef k * Real.sqrt s + ∑ i ∈ Finset.range I,
      Real.sqrt (2 ^ i * s) * (Real.exp (-2 * (2 ^ i * s)) + Real.exp (-(2 ^ i * s))) ≤ 89 / 50 :=
  @UpperQuarter.band_offset_le

example : ∀ {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (K : ℕ),
    ∑ l ∈ Finset.range K, Real.sqrt (Uniform713.cap l * d ^ 2) * UpperQuarter.quarterWeight l d ≤
      89 / 50 :=
  @UpperQuarter.quarter_grid_le

example : ∀ (L : ℕ) (p : unitInterval) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (s : ℝ),
    (∀ L, (Tier2.tapeMeasure p).real {ω | Tier2.Model.decision
      (fun k => Uniform713.dyadicMean Tier2.observations k ω) L ≠ s} ≤
        Tier2.Model.errorUnionBound L d) →
    (∀ L, (Tier2.tapeMeasure p).real {ω | ∃ k < L,
      Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L) <
        |Uniform713.dyadicMean Tier2.observations k ω - 1/2|} ≤ UpperSign.earlyBound L d) →
    (∫ ω, (Uniform713.increment (fun k => Tier2.Model.decision
      (fun j => Uniform713.dyadicMean Tier2.observations j ω) k) L) ^ 2 ∂Tier2.tapeMeasure p) ≤
      min 1 (UpperQuarter.quarterWeight L d + UpperDisagreement.stopError L d +
        UpperDisagreement.stopError (L - 1) d) :=
  @UpperQuarter.quarter_increment_le

example : ∀ (L : ℕ) {d : ℝ}, 0 < d → d ≤ 1 / 2 → ∀ (e : ℕ → ℝ),
    (∀ l ≤ L, e l ≤ min 1 (UpperQuarter.quarterWeight l d + UpperDisagreement.stopError l d +
      UpperDisagreement.stopError (l - 1) d)) →
    ∑ l ∈ Finset.range (L + 1), e l / pLevel l ≤
      (13 / 2) * min (Real.sqrt (Uniform713.cap L)) d⁻¹ +
        (129 / 25) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  @UpperQuarter.quarter_levelSum_le

example : ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    secondMomentK 1 1 L d S ≤ (13/2) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ +
      (129/25) * (if Uniform713.cap L * d ^ 2 ≤ 1 then Real.sqrt (Uniform713.cap L) else 0) :=
  UpperQuarter.secondMomentK_le

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (∫⁻ z, ENNReal.ofReal ((BlindUpper.cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂BlindUpper.calibrationLaw (BlindUpper.callMeasure μ q)) ≤
      ENNReal.ofReal ((147/4)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) :=
  @UpperQuarter.cutoffBatch_mse

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (13 * modulus μ (1 / Real.sqrt B)) :=
  @UpperQuarter.budgetMixture_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-quarter module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperQuarter/{name}.lean")
        roots.extend(public_names(source, f"UpperQuarter/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-quarter declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-quarter target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-quarter statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperQuarter.{statement} := UpperQuarter.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperQuarter\.{re.escape(name)}\n", EXACT)) != 1:
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
    print("Both upper-quarter target statements are certified")


if __name__ == "__main__":
    main()
