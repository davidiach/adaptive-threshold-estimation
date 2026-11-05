import ThresholdHC.AdditiveConfidence.InputMixture

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

def tapeStatisticLaw {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (κ : Measure unitInterval) (A : StoppedProcedure R E) (n : ℕ) :
    Measure (Fin (n+1) × Fin (n+1)) :=
  ((ν.prod (parameterTapeLaw κ)).map (cappedTranscript A n)).map
    (fun z => stoppedStatistic n z.2)

instance tapeStatisticLaw_finite {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsFiniteMeasure ν] (κ : Measure unitInterval) [IsFiniteMeasure κ]
    (A : StoppedProcedure R E) (n : ℕ) : IsFiniteMeasure (tapeStatisticLaw ν κ A n) := by
  unfold tapeStatisticLaw
  infer_instance

theorem tapeStatisticLaw_mass {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (κ : Measure unitInterval) [IsFiniteMeasure κ]
    (A : StoppedProcedure R E) (n : ℕ) :
    (tapeStatisticLaw ν κ A n).real Set.univ = κ.real Set.univ := by
  have hT : Measurable (fun z : R × CappedWord n => stoppedStatistic n z.2) :=
    (measurable_of_countable (stoppedStatistic n)).comp measurable_snd
  have ht : (parameterTapeLaw κ) Set.univ = κ Set.univ := by
    rw [parameterTapeLaw,Measure.map_apply measurable_uniformCoinTape MeasurableSet.univ,
      Set.preimage_univ,← Set.univ_prod_univ,Measure.prod_prod,
      measure_univ (μ := uniformTapeMeasure),mul_one]
  simp only [tapeStatisticLaw,Measure.real,Measure.map_apply hT MeasurableSet.univ,
    Set.preimage_univ,Measure.map_apply (measurable_cappedTranscript A n) MeasurableSet.univ]
  rw [← Set.univ_prod_univ,Measure.prod_prod,measure_univ (μ := ν),one_mul,ht]

theorem capped_statistic_tape {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : SignLaw) (A : StoppedProcedure R E) (n : ℕ) :
    cappedStatisticLaw μ ν p₀ p₁ (signUnit q) A n =
      tapeStatisticLaw ν (populationParameterLaw μ p₀ p₁ (signUnit q)) A n := by
  rw [cappedStatisticLaw,populationInput_capped_law μ ν _ _ _ h₀ h₁ (measurable_signUnit q)]
  rfl

theorem GapMixture.statistic_law {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2) (A : StoppedProcedure R E) (n : ℕ) :
    cappedStatisticLaw μ ν p₀ p₁ (signUnit (M.mixedSign q)) A n =
      tapeStatisticLaw ν (M.residual.map p₀) A n+
        ∑ i, M.weight i • cappedStatisticLaw (M.law i) ν p₀ p₁ (signUnit (q i)) A n := by
  have hT : Measurable (fun z : R × CappedWord n => stoppedStatistic n z.2) :=
    (measurable_of_countable (stoppedStatistic n)).comp measurable_snd
  rw [capped_statistic_tape μ ν p₀ p₁ h₀ h₁,tapeStatisticLaw,M.input_law ν p₀ p₁ h₀ h₁ q hq]
  simp only [Measure.map_add _ _ (measurable_cappedTranscript A n),
    Measure.map_add _ _ hT,
    Measure.map_finset_sum' (measurable_cappedTranscript A n).aemeasurable,
    Measure.map_finset_sum' hT.aemeasurable,
    Measure.map_smul _ (measurable_cappedTranscript A n).aemeasurable,
    Measure.map_smul _ hT.aemeasurable,
    capped_statistic_tape _ _ _ _ h₀ h₁]
  rfl

end ThresholdHC.AdditiveConfidence
