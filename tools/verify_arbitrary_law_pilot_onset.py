"""Audit the pilot's work estimates (A12), its onset and the floors of the selection functional.

Every definition and theorem of the pilot-onset module is restated in full, so
a changed definition, hypothesis or constant is an elaboration error, and the
transitive axioms of every declaration are reported. A declaration in that
module that is not registered here is an error. Prints the kernel report;
writes nothing.
"""

import subprocess
from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.ArbitraryLawAdaptation.PilotOnset"
SOURCES = [LEAN / "ThresholdHC/ArbitraryLawAdaptation" / (name + ".lean")
           for name in ("PilotOnset",)]
NAMES = [
    "PilotOnset", "lowest_gap_split", "pilot_onset_exists", "pilotOnset_eventually",
    "pilotOnset_tailOnset", "pilotOnset_small", "reciprocal_le_pilotBudget",
    "geometric_le_pilotBudget", "tailWorkEnvelope_le_tail", "tailWorkEnvelope_le_core",
    "tailKernel_scale", "tailModulus_scale", "integrable_tailWorkEnvelope", "work_split",
    "quantile_work_le", "core_work_le", "pilot_quantile_work", "pilot_core_work", "pilot_work_le",
    "quantile_tail_floor", "pilot_work_le_oracle", "inv_pilotCoinCap_le",
    "pilot_coin_cap_le_oracle", "pilotOnset_floor", "pilotOnset_coin_cap",
]


def declared_names():
    """Every declaration of the module, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += DECLARATION.findall(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing pilot-onset declaration")
    source = """
import ThresholdHC.ArbitraryLawAdaptation.PilotOnset
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailQuantile

example : ∀ (μ : Measure Gap) (ρ : ℝ) (J : ℕ), PilotOnset μ ρ J ↔
    2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 ≤ Real.sqrt ρ :=
  fun _ _ _ => Iff.rfl

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
    quantileTail μ ρ + quantileCore μ ρ = μ ∧
      quantileTail μ ρ Set.univ = ENNReal.ofReal ρ ∧
      0 < quantileThreshold μ ρ ∧
      (∀ᵐ d : Gap ∂quantileTail μ ρ, (d : ℝ) ≤ quantileThreshold μ ρ) ∧
      ∀ᵐ d : Gap ∂quantileCore μ ρ, quantileThreshold μ ρ ≤ (d : ℝ) := @lowest_gap_split
example : ∀ {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ),
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      2048 * ((J : ℝ) + 1) ^ 3 * (1 / 2) ^ J / a ^ 2 ≤ Real.sqrt ρ := @pilot_onset_exists
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → PilotOnset μ ρ J := @pilotOnset_eventually
example : ∀ {μ : Measure Gap} {ρ : ℝ} {J : ℕ} (h : PilotOnset μ ρ J),
    TailOnset μ ρ J := @pilotOnset_tailOnset
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {J : ℕ} (h : PilotOnset μ ρ J),
    2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ := @pilotOnset_small
example : ∀ (J j : ℕ),
    (4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1)) ≤ (pilotBudget J j : ℝ) := @reciprocal_le_pilotBudget
example : ∀ (J j : ℕ),
    (2 : ℝ) ^ (J + j - 2) ≤ (pilotBudget J j : ℝ) := @geometric_le_pilotBudget
example : ∀ (j : ℕ) (d : Gap),
    tailWorkEnvelope j d ≤ 2048 * 4 ^ j * min 1 ((1 / 2) ^ j / (d : ℝ)) := @tailWorkEnvelope_le_tail
example : ∀ (j : ℕ) {a : ℝ} (ha : 0 < a) (d : Gap) (had : a ≤ (d : ℝ)),
    tailWorkEnvelope j d ≤ 1024 * ((j : ℝ) + 1) / a ^ 2 := @tailWorkEnvelope_le_core
example : ∀ {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (d : Gap),
    min 1 (s / (d : ℝ)) ≤ s / t * min 1 (t / (d : ℝ)) := @tailKernel_scale
example : ∀ (ν : Measure Gap) [IsFiniteMeasure ν] {t s : ℝ} (ht : 0 < t) (hts : t ≤ s),
    tailModulus ν s ≤ s / t * tailModulus ν t := @tailModulus_scale
example : ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ] (j : ℕ),
    Integrable (fun d : Gap => tailWorkEnvelope j d) ξ := @integrable_tailWorkEnvelope
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ),
    ∫ d : Gap, tailWorkEnvelope j d ∂μ =
      ∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ +
      ∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ := @work_split
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ),
    ∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ ≤
      2048 * 4 ^ j * tailModulus (quantileTail μ ρ) ((1 / 2) ^ j) := @quantile_work_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ),
    ∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ ≤
      1024 * ((j : ℝ) + 1) / (quantileThreshold μ ρ) ^ 2 := @core_work_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J),
    (∫ d : Gap, tailWorkEnvelope j d ∂quantileTail μ ρ) / (pilotBudget J j : ℝ) ≤
      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) := @pilot_quantile_work
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J),
    (∫ d : Gap, tailWorkEnvelope j d ∂quantileCore μ ρ) / (pilotBudget J j : ℝ) ≤
      2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 := @pilot_core_work
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J),
    (∫ d : Gap, tailWorkEnvelope j d ∂μ) / (pilotBudget J j : ℝ) ≤
      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
      2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 := @pilot_work_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (J : ℕ),
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) ((1 / 2) ^ J)) ≤
      ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @quantile_tail_floor
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) (hon : PilotOnset μ ρ J),
    ENNReal.ofReal ((∫ d : Gap, tailWorkEnvelope j d ∂μ) / (pilotBudget J j : ℝ)) ≤
      8193 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @pilot_work_le_oracle
example : ∀ (J : ℕ) {ρ : ℝ} (hρ : 0 < ρ),
    1 / (pilotCoinCap J ρ : ℝ) ≤ Real.sqrt ρ * (1 / 2) ^ J / 8 := @inv_pilotCoinCap_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hsmall : 2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ),
    ENNReal.ofReal (16 / (pilotCoinCap J ρ : ℝ)) ≤ ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @pilot_coin_cap_le_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J),
    ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) ≤ ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @pilotOnset_floor
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J),
    ENNReal.ofReal (16 / (pilotCoinCap J ρ : ℝ)) ≤ ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @pilotOnset_coin_cap
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each pilot-onset declaration needs exactly one restated statement")
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in NAMES}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", MODULE], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
