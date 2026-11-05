import ThresholdHC.AdditiveConfidence.NegativeMass

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.ConfidenceLocalization

theorem parameter_positive_negative (μ : Measure Gap) [IsProbabilityMeasure μ]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (q : SignLaw) :
    populationParameterLaw μ p₀ p₁ (signUnit q) =
      (positiveMeasure μ q).map p₁+(positiveMeasure μ (complementSign q)).map p₀ := by
  apply Measure.ext
  intro S hS
  have hF : Measurable (S.indicator (1 : unitInterval → ℝ≥0∞)) := measurable_const.indicator hS
  have hq : Measurable (fun d => ENNReal.ofReal (q.val d)) :=
    ENNReal.measurable_ofReal.comp q.property.1
  have hn : Measurable (fun d => ENNReal.ofReal ((complementSign q).val d)) :=
    ENNReal.measurable_ofReal.comp (complementSign q).property.1
  have hF₀ : Measurable (fun d => S.indicator (1 : unitInterval → ℝ≥0∞) (p₀ d)) := hF.comp h₀
  have hF₁ : Measurable (fun d => S.indicator (1 : unitInterval → ℝ≥0∞) (p₁ d)) := hF.comp h₁
  rw [← lintegral_indicator_one hS,← lintegral_indicator_one hS,lintegral_add_measure,
    parameter_lintegral μ p₀ p₁ (signUnit q) h₀ h₁ (measurable_signUnit q) _ hF,
    lintegral_map hF h₁,lintegral_map hF h₀,
    positiveMeasure,positiveMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hq hF₁,
    lintegral_withDensity_eq_lintegral_mul _ hn hF₀]
  exact lintegral_add_left
    ((ENNReal.measurable_ofReal.comp q.property.1).mul (hF.comp h₁)) _

theorem GapMixture.parameter_law {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ)
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2) :
    populationParameterLaw μ p₀ p₁ (signUnit (M.mixedSign q)) =
      M.residual.map p₀+∑ i, M.weight i • populationParameterLaw (M.law i) p₀ p₁ (signUnit (q i)) := by
  rw [parameter_positive_negative μ p₀ p₁ h₀ h₁,M.mixedSign_density q hq,
    M.mixedSign_complement q hq]
  simp only [GapMixture.positiveMass,Measure.map_add _ _ h₀,
    Measure.map_finset_sum' h₀.aemeasurable,Measure.map_finset_sum' h₁.aemeasurable,
    Measure.map_smul _ h₀.aemeasurable,Measure.map_smul _ h₁.aemeasurable,
    parameter_positive_negative _ _ _ h₀ h₁,smul_add,Finset.sum_add_distrib]
  ac_rfl

end ThresholdHC.AdditiveConfidence
