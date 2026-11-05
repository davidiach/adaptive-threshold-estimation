import ThresholdHC.AdditiveConfidence.ParameterMixture

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

instance parameterTapeLaw_finite (κ : Measure unitInterval) [IsFiniteMeasure κ] :
    IsFiniteMeasure (parameterTapeLaw κ) := by
  unfold parameterTapeLaw
  infer_instance

theorem tape_law_sum {I : Type} [Fintype I] (κ : I → Measure unitInterval) :
    parameterTapeLaw (∑ i, κ i) = ∑ i, parameterTapeLaw (κ i) := by
  simp only [parameterTapeLaw,← Measure.sum_fintype,Measure.prod_sum_left,
    Measure.map_sum measurable_uniformCoinTape.aemeasurable]

theorem input_law_mixture {I R : Type} [Fintype I] [MeasurableSpace R]
    (ν : Measure R) [SFinite ν] (η : Measure unitInterval) [IsFiniteMeasure η]
    (κ : I → Measure unitInterval) [∀ i, IsFiniteMeasure (κ i)] (w : I → ℝ≥0) :
    ν.prod (parameterTapeLaw (η+∑ i, w i • κ i)) =
      ν.prod (parameterTapeLaw η)+∑ i, w i • (ν.prod (parameterTapeLaw (κ i))) := by
  have ht : parameterTapeLaw (η+∑ i, w i • κ i) =
      parameterTapeLaw η+∑ i, w i • parameterTapeLaw (κ i) := by
    rw [parameterTapeLaw,Measure.add_prod,Measure.map_add _ _ measurable_uniformCoinTape]
    change parameterTapeLaw η+parameterTapeLaw (∑ i, w i • κ i) = _
    rw [tape_law_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [parameterTapeLaw,Measure.prod_smul_left,
      Measure.map_smul _ measurable_uniformCoinTape.aemeasurable]
  rw [ht,Measure.prod_add]
  congr 1
  rw [← Measure.sum_fintype,Measure.prod_sum_right,Measure.sum_fintype]
  simp only [Measure.prod_smul_right]

theorem GapMixture.input_law {I R : Type} [Fintype I] [MeasurableSpace R] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (ν : Measure R) [SFinite ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2) :
    ν.prod (parameterTapeLaw (populationParameterLaw μ p₀ p₁ (signUnit (M.mixedSign q)))) =
      ν.prod (parameterTapeLaw (M.residual.map p₀))+
        ∑ i, M.weight i • (ν.prod (parameterTapeLaw (populationParameterLaw (M.law i) p₀ p₁ (signUnit (q i))))) := by
  let (i : I) : IsProbabilityMeasure (populationParameterLaw (M.law i) p₀ p₁ (signUnit (q i))) :=
    populationParameterLaw_probability _ _ _ _ h₀ h₁ (measurable_signUnit _)
  rw [M.parameter_law p₀ p₁ h₀ h₁ q hq,input_law_mixture]

end ThresholdHC.AdditiveConfidence
