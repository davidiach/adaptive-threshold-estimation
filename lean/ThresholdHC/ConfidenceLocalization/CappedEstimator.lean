import ThresholdHC.ConfidenceLocalization.Obstruction

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem regularized_capped_estimator {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (hsep : ∀ q r : D → unitInterval, CappedPrior μ (c : ℝ) q → CappedPrior μ (c : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n →
      (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) < 2*ε) :
    ∃ Z : StoppedProcedure R ℝ, Z.stop = A.stop ∧
      (∃ C : ℝ, ∀ z, |Z.output z| ≤ C) ∧
      ∀ q : D → unitInterval, CappedPrior μ (c : ℝ) q →
      MemLp (Z.output ∘ populationInput p₀ p₁ q) 2 (populationMeasure μ ν) ∧
      |populationMean μ ν p₀ p₁ q Z-(∫ d, (q d : ℝ) ∂μ)| ≤ 6*ε ∧
      evariance (Z.output ∘ populationInput p₀ p₁ q) (populationMeasure μ ν) ≤
        ENNReal.ofReal (18*(n : ℝ)*ε^2) ∧
      populationExpectedWork μ ν p₀ p₁ q Z = populationExpectedWork μ ν p₀ p₁ q A := by
  obtain ⟨f,hf⟩ := regularized_observation_score μ ν p₀ p₁ h₀ h₁ A m hcap c hc0 hc ε hε n hsep
  let Z := cappedStatisticProcedure A m hcap f
  refine ⟨Z,rfl,⟨∑ i, |f i|,?_⟩,?_⟩
  · intro z
    change |f _| ≤ ∑ i, |f i|
    exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ _)
  · intro q hq
    let ξ := cappedStatisticLaw μ ν p₀ p₁ q A m
    let : IsProbabilityMeasure ξ := cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq.1 A m
    have hZ : Measurable (Z.output ∘ populationInput p₀ p₁ q) :=
      Z.measurable_output.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq.1)
    have hlaw := cappedStatisticProcedure_output_law μ ν p₀ p₁ q h₀ h₁ hq.1 A m hcap f
    have hm : populationMean μ ν p₀ p₁ q Z = ∫ i, f i ∂ξ := by
      calc
        _ = ∫ y : ℝ, y ∂(populationMeasure μ ν).map (Z.output ∘ populationInput p₀ p₁ q) :=
          (integral_map hZ.aemeasurable measurable_id.aestronglyMeasurable).symm
        _ = ∫ y : ℝ, y ∂ξ.map f := by rw [hlaw]
        _ = _ := integral_map (measurable_of_countable f).aemeasurable measurable_id.aestronglyMeasurable
    have hv : evariance (Z.output ∘ populationInput p₀ p₁ q) (populationMeasure μ ν) = evariance f ξ := by
      calc
        _ = evariance id ((populationMeasure μ ν).map (Z.output ∘ populationInput p₀ p₁ q)) :=
          (evariance_map_measurable (populationMeasure μ ν) _ id hZ measurable_id).symm
        _ = evariance id (ξ.map f) := by rw [hlaw]
        _ = _ := evariance_map_measurable ξ f id (measurable_of_countable f) measurable_id
    refine ⟨cappedStatisticProcedure_memLp μ ν p₀ p₁ q h₀ h₁ hq.1 A m hcap f,?_,?_,rfl⟩
    · rw [hm]
      exact (hf q hq).1
    · rw [hv]
      exact (hf q hq).2

end ThresholdHC.ConfidenceLocalization
