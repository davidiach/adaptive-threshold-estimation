import ThresholdHC.CriticalEntropy.CriticalGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

def cappedStatisticProcedure {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (f : Fin (m+1) × Fin (m+1) → ℝ) : StoppedProcedure R ℝ where
  stop := A.stop
  output := fun z => f (stoppedStatistic m (cappedTranscript A m z).2)
  measurable_stop := A.measurable_stop
  measurable_output := (measurable_of_countable f).comp
    ((measurable_of_countable (stoppedStatistic m)).comp
      (measurable_snd.comp (measurable_cappedTranscript A m)))
  stopPrefix := A.stopPrefix
  measurable_stopPrefix := A.measurable_stopPrefix
  stop_observable := A.stop_observable
  outputPrefix := fun n z => if hn : n ≤ m then
    f (stoppedStatistic m ⟨⟨n,Nat.lt_succ_of_le hn⟩,z.2⟩) else 0
  measurable_outputPrefix := by
    intro n
    split_ifs with hn
    · exact (measurable_of_countable (fun w : Fin n → Bool =>
        f (stoppedStatistic m ⟨⟨n,Nat.lt_succ_of_le hn⟩,w⟩))).comp measurable_snd
    · exact measurable_const
  output_observable := by
    intro n z hz
    have hn : n ≤ m := by
      have h := hcap z
      rw [hz] at h
      exact_mod_cast h
    rw [cappedTranscript_of_stop A m n hn z hz,dite_eq_left hn]

theorem cappedStatisticProcedure_work {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (f : Fin (m+1) × Fin (m+1) → ℝ) :
    populationExpectedWork μ ν p₀ p₁ q (cappedStatisticProcedure A m hcap f) =
      populationExpectedWork μ ν p₀ p₁ q A := rfl

theorem cappedStatisticProcedure_output_law {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (f : Fin (m+1) × Fin (m+1) → ℝ) :
    (populationMeasure μ ν).map ((cappedStatisticProcedure A m hcap f).output ∘
      populationInput p₀ p₁ q) = (cappedStatisticLaw μ ν p₀ p₁ q A m).map f := by
  have hT : Measurable (fun z : R × CappedWord m => stoppedStatistic m z.2) :=
    (measurable_of_countable (stoppedStatistic m)).comp measurable_snd
  have hfT : Measurable (fun z : R × CappedWord m => f (stoppedStatistic m z.2)) :=
    (measurable_of_countable f).comp hT
  rw [cappedStatisticLaw,Measure.map_map (measurable_of_countable f) hT]
  change _ = (cappedTranscriptLaw μ ν p₀ p₁ q A m).map (fun z => f (stoppedStatistic m z.2))
  rw [cappedTranscriptLaw,Measure.map_map hfT
    ((measurable_cappedTranscript A m).comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq))]
  rfl

theorem cappedStatisticProcedure_memLp {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (f : Fin (m+1) × Fin (m+1) → ℝ) :
    MemLp ((cappedStatisticProcedure A m hcap f).output ∘ populationInput p₀ p₁ q) 2
      (populationMeasure μ ν) := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by
    unfold populationMeasure
    infer_instance
  apply MemLp.of_bound
    (((cappedStatisticProcedure A m hcap f).measurable_output).comp
      (measurable_populationInput p₀ p₁ q h₀ h₁ hq)).aestronglyMeasurable (∑ i, ‖f i‖)
  apply ae_of_all
  intro z
  exact Finset.single_le_sum (fun i hi => norm_nonneg (f i)) (Finset.mem_univ _)

theorem population_capped_work_le {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    populationExpectedWork μ ν p₀ p₁ q A ≤ (m : ℝ≥0∞) := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by
    unfold populationMeasure
    infer_instance
  calc
    _ ≤ ∫⁻ z, (m : ℝ≥0∞) ∂populationMeasure μ ν := by
      apply lintegral_mono
      intro z
      change stoppedProcedureWork A (populationInput p₀ p₁ q z) ≤ (m : ℝ≥0∞)
      rw [capped_transcript_work A m _ (hcap _)]
      exact_mod_cast Nat.le_of_lt_succ (stoppedStatistic m
        (cappedTranscript A m (populationInput p₀ p₁ q z)).2).1.isLt
    _ = _ := by simp

end ThresholdHC.CriticalEntropy
