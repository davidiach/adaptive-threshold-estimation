import ThresholdHC.ConfidenceLocalization.StatisticGeometry
import ThresholdHC.CriticalEntropy.PopulationTapeLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem parameter_lintegral {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (F : unitInterval → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂populationParameterLaw μ p₀ p₁ q) =
      ∫⁻ d, ENNReal.ofReal (q d : ℝ)*F (p₁ d) + ENNReal.ofReal (1-(q d : ℝ))*F (p₀ d) ∂μ := by
  have hm := measurable_mixtureParameter p₀ p₁ q h₀ h₁ hq
  rw [populationParameterLaw,lintegral_map hF hm]
  rw [lintegral_prod (fun z : D × ℝ => F (mixtureParameter p₀ p₁ q z)) (hF.comp hm).aemeasurable]
  exact lintegral_congr (fun d => mixtureParameter_lintegral p₀ p₁ q d F hF)

/-- A strictly positive constant sign prior dominates every conditional prior,
even when a Bernoulli parameter lies at zero or one. -/
theorem parameter_law_const_domination {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (c : unitInterval) (hc : (c : ℝ) ≤ 1/2) :
    ENNReal.ofReal (c : ℝ) • populationParameterLaw μ p₀ p₁ q ≤
      populationParameterLaw μ p₀ p₁ (fun _ => c) := by
  refine Measure.le_iff.mpr ?_
  intro S hS
  have hF : Measurable (S.indicator (1 : unitInterval → ℝ≥0∞)) := measurable_const.indicator hS
  rw [← lintegral_indicator_one hS,← lintegral_indicator_one hS,
    lintegral_smul_measure,parameter_lintegral μ p₀ p₁ q h₀ h₁ hq _ hF,
    parameter_lintegral μ p₀ p₁ (fun _ => c) h₀ h₁ measurable_const _ hF]
  simp only [smul_eq_mul]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro d
  simp only [mul_add,← mul_assoc]
  apply add_le_add
  · apply mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_mul c.property.1]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_of_le_one_right c.property.1 (q d).property.2
  · apply mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_mul c.property.1]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [c.property.1,(q d).property.1,(q d).property.2]

end ThresholdHC.ConfidenceLocalization
