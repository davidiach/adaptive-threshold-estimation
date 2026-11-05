import ThresholdHC.ConfidenceLocalization.PriorMidpoint
import ThresholdHC.ConfidenceLocalization.PriorDomination
import ThresholdHC.CriticalEntropy.PopulationLocalWork

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem tape_midpoint_law (κ τ : Measure unitInterval)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure τ] :
    parameterTapeLaw ((1/2 : ℝ≥0) • κ + (1/2 : ℝ≥0) • τ) =
      (1/2 : ℝ≥0) • parameterTapeLaw κ + (1/2 : ℝ≥0) • parameterTapeLaw τ := by
  simp only [parameterTapeLaw,Measure.add_prod,Measure.prod_smul_left,
    Measure.map_add _ _ measurable_uniformCoinTape,
    Measure.map_smul _ measurable_uniformCoinTape.aemeasurable]

theorem capped_law_midpoint {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (n : ℕ) :
    cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q r) A n =
      (1/2 : ℝ≥0) • cappedTranscriptLaw μ ν p₀ p₁ q A n +
      (1/2 : ℝ≥0) • cappedTranscriptLaw μ ν p₀ p₁ r A n := by
  let := populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  let := populationParameterLaw_probability μ p₀ p₁ r h₀ h₁ hr
  rw [populationInput_capped_law μ ν _ _ _ h₀ h₁ (measurable_midpointPrior q r hq hr),
    populationInput_capped_law μ ν _ _ _ h₀ h₁ hq,
    populationInput_capped_law μ ν _ _ _ h₀ h₁ hr,
    parameter_midpoint_law μ p₀ p₁ q r h₀ h₁ hq hr,tape_midpoint_law]
  simp only [Measure.prod_add,Measure.prod_smul_right,
    Measure.map_add _ _ (measurable_cappedTranscript A n),
    Measure.map_smul _ (measurable_cappedTranscript A n).aemeasurable]

theorem statistic_law_midpoint {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (n : ℕ) :
    cappedStatisticLaw μ ν p₀ p₁ (midpointPrior q r) A n =
      (1/2 : ℝ≥0) • cappedStatisticLaw μ ν p₀ p₁ q A n +
      (1/2 : ℝ≥0) • cappedStatisticLaw μ ν p₀ p₁ r A n := by
  have hT : Measurable (fun z : R × CappedWord n => stoppedStatistic n z.2) :=
    (measurable_of_countable (stoppedStatistic n)).comp measurable_snd
  rw [cappedStatisticLaw,capped_law_midpoint μ ν p₀ p₁ q r h₀ h₁ hq hr A n,
    Measure.map_add _ _ hT,Measure.map_smul _ hT.aemeasurable,Measure.map_smul _ hT.aemeasurable]
  rfl

theorem tape_law_mono (κ τ : Measure unitInterval) (h : κ ≤ τ) :
    parameterTapeLaw κ ≤ parameterTapeLaw τ :=
  Measure.map_mono (Measure.prod_mono h le_rfl) measurable_uniformCoinTape

theorem tape_law_smul (κ : Measure unitInterval) (c : ℝ≥0∞) :
    parameterTapeLaw (c • κ) = c • parameterTapeLaw κ := by
  simp only [parameterTapeLaw,Measure.prod_smul_left,
    Measure.map_smul _ measurable_uniformCoinTape.aemeasurable]

theorem capped_law_const_domination {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (c : unitInterval) (hc : (c : ℝ) ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ) :
    ENNReal.ofReal (c : ℝ) • cappedTranscriptLaw μ ν p₀ p₁ q A n ≤
      cappedTranscriptLaw μ ν p₀ p₁ (fun _ => c) A n := by
  let := populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  let := populationParameterLaw_probability μ p₀ p₁ (fun _ => c) h₀ h₁ measurable_const
  have h := tape_law_mono _ _ (parameter_law_const_domination μ p₀ p₁ q h₀ h₁ hq c hc)
  rw [tape_law_smul] at h
  have hp := Measure.prod_mono (μ := ν) le_rfl h
  rw [Measure.prod_smul_right] at hp
  have hm := Measure.map_mono hp (measurable_cappedTranscript A n)
  rw [Measure.map_smul _ (measurable_cappedTranscript A n).aemeasurable,
    ← populationInput_capped_law μ ν _ _ _ h₀ h₁ hq,
    ← populationInput_capped_law μ ν _ _ _ h₀ h₁ measurable_const] at hm
  exact hm

theorem statistic_law_const_domination {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (c : unitInterval) (hc : (c : ℝ) ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ) :
    ENNReal.ofReal (c : ℝ) • cappedStatisticLaw μ ν p₀ p₁ q A n ≤
      cappedStatisticLaw μ ν p₀ p₁ (fun _ => c) A n := by
  have hT : Measurable (fun z : R × CappedWord n => stoppedStatistic n z.2) :=
    (measurable_of_countable (stoppedStatistic n)).comp measurable_snd
  have h := Measure.map_mono (capped_law_const_domination μ ν p₀ p₁ q h₀ h₁ hq c hc A n) hT
  rw [Measure.map_smul _ hT.aemeasurable] at h
  exact h

end ThresholdHC.ConfidenceLocalization
