
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
#print axioms ThresholdHC.ArbitraryLawAdaptation.PilotOnset
#print axioms ThresholdHC.ArbitraryLawAdaptation.core_work_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.geometric_le_pilotBudget
#print axioms ThresholdHC.ArbitraryLawAdaptation.integrable_tailWorkEnvelope
#print axioms ThresholdHC.ArbitraryLawAdaptation.inv_pilotCoinCap_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.lowest_gap_split
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotOnset_coin_cap
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotOnset_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotOnset_floor
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotOnset_small
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotOnset_tailOnset
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilot_coin_cap_le_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilot_core_work
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilot_onset_exists
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilot_quantile_work
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilot_work_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilot_work_le_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.quantile_tail_floor
#print axioms ThresholdHC.ArbitraryLawAdaptation.quantile_work_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.reciprocal_le_pilotBudget
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailKernel_scale
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailModulus_scale
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWorkEnvelope_le_core
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWorkEnvelope_le_tail
#print axioms ThresholdHC.ArbitraryLawAdaptation.work_split
