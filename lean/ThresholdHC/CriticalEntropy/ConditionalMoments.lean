import ThresholdHC.CriticalEntropy.PopulationVariance

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.CriticalEntropy

theorem conditional_moment_pair_integrable {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞) :
    Integrable (fun d => (conditionalSecondMoment ν (p₀ d) A).toReal) μ ∧
    Integrable (fun d => (conditionalSecondMoment ν (p₁ d) A).toReal) μ ∧
    (∀ᵐ d ∂μ, conditionalSecondMoment ν (p₀ d) A ≠ ∞ ∧
      conditionalSecondMoment ν (p₁ d) A ≠ ∞) := by
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  have hi := population_finite_components μ ν p₀ p₁ h₀ h₁ c hc _ hsq hm₀ hm₁
  exact ⟨integrable_toReal_of_lintegral_ne_top
      ((measurable_conditionalSecondMoment ν A).comp h₀).aemeasurable hi.1,
    integrable_toReal_of_lintegral_ne_top
      ((measurable_conditionalSecondMoment ν A).comp h₁).aemeasurable hi.2,
    population_ae_finite_components μ ν p₀ p₁ h₀ h₁ c hc _ hsq hm₀ hm₁⟩

/-- Real-valued disintegration is used only after integrated conditional
moments are proved finite from actual population laws. -/
theorem population_second_moment_real_formula {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (q : D → unitInterval) (hq : Measurable q) :
    (populationSecondMoment μ ν p₀ p₁ q A).toReal =
      ∫ d, (q d : ℝ)*(conditionalSecondMoment ν (p₁ d) A).toReal +
        (1-(q d : ℝ))*(conditionalSecondMoment ν (p₀ d) A).toReal ∂μ := by
  have ha := (conditional_moment_pair_integrable μ ν p₀ p₁ h₀ h₁ c hc A hm₀ hm₁).2.2
  have hsum : Measurable (fun d => ENNReal.ofReal (q d : ℝ)*conditionalSecondMoment ν (p₁ d) A +
      ENNReal.ofReal (1-(q d : ℝ))*conditionalSecondMoment ν (p₀ d) A) := by
    exact ((ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp hq)).mul
      ((measurable_conditionalSecondMoment ν A).comp h₁)).add
      ((ENNReal.measurable_ofReal.comp (measurable_const.sub (measurable_subtype_coe.comp hq))).mul
        ((measurable_conditionalSecondMoment ν A).comp h₀))
  have haf : ∀ᵐ d ∂μ, ENNReal.ofReal (q d : ℝ)*conditionalSecondMoment ν (p₁ d) A +
      ENNReal.ofReal (1-(q d : ℝ))*conditionalSecondMoment ν (p₀ d) A < ∞ := by
    filter_upwards [ha] with d hd
    exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd.2,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd.1⟩)
  rw [population_second_moment_formula μ ν p₀ p₁ q h₀ h₁ hq,
    ← integral_toReal hsum.aemeasurable haf]
  apply integral_congr_ae
  filter_upwards [ha] with d hd
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd.2)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd.1)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (q d).property.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (q d).property.2)]

end ThresholdHC.CriticalEntropy
