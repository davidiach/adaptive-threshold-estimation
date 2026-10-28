import ThresholdHC.CriticalEntropy.GoodGapModel
import ThresholdHC.CriticalEntropy.ConditionalMoments

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem measurable_halfPrior {D : Type} [MeasurableSpace D] (E : Set D)
    (hE : MeasurableSet E) : Measurable (halfPrior E) := by
  unfold halfPrior
  exact Measurable.ite hE measurable_const measurable_const

theorem halfPrior_le_half {D : Type} (E : Set D) (d : D) :
    (halfPrior E d : ℝ) ≤ 1/2 := by
  simp only [halfPrior]
  split_ifs <;> norm_num

theorem halfPrior_integral {D : Type} [MeasurableSpace D]
    (μ : Measure D) (E : Set D) (hE : MeasurableSet E) :
    (∫ d, (halfPrior E d : ℝ) ∂μ) = μ.real E/2 := by
  have he : (fun d => (halfPrior E d : ℝ)) =
      fun d => (1/2 : ℝ)*E.indicator (fun _ => (1 : ℝ)) d := by
    funext d
    by_cases hd : d ∈ E <;> simp [halfPrior,hd]
  rw [he,integral_const_mul,integral_indicator hE]
  simp only [setIntegral_const,smul_eq_mul,mul_one]
  ring

theorem cappedPrior_const {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ) (c : unitInterval)
    (hc : (c : ℝ) ≤ 1/2) (hcρ : (c : ℝ) ≤ ρ) :
    CappedPrior μ ρ (fun _ => c) := by
  refine ⟨measurable_const,fun _ => hc,?_⟩
  simpa using hcρ

theorem cappedPrior_half {D : Type} [MeasurableSpace D]
    (μ : Measure D) (ρ : ℝ) (E : Set D) (hE : MeasurableSet E)
    (hm : μ.real E ≤ 2*ρ) : CappedPrior μ ρ (halfPrior E) := by
  refine ⟨measurable_halfPrior E hE,halfPrior_le_half E,?_⟩
  rw [halfPrior_integral μ E hE]
  linarith

/-- Exact perturbation at a set of gaps, with probability one half on the set
and zero elsewhere. Both conditional functions are genuinely integrable. -/
theorem halfPrior_weighted_integral {D : Type} [MeasurableSpace D]
    (μ : Measure D) (E : Set D) (hE : MeasurableSet E)
    (f₀ f₁ : D → ℝ) (h₀ : Integrable f₀ μ) (h₁ : Integrable f₁ μ) :
    (∫ d, (halfPrior E d : ℝ)*f₁ d+(1-(halfPrior E d : ℝ))*f₀ d ∂μ) =
      (∫ d, f₀ d ∂μ)+(1/2)*(∫ d in E, f₁ d-f₀ d ∂μ) := by
  have he : (fun d => (halfPrior E d : ℝ)*f₁ d+(1-(halfPrior E d : ℝ))*f₀ d) =
      fun d => f₀ d+(1/2)*E.indicator (fun x => f₁ x-f₀ x) d := by
    funext d
    by_cases hd : d ∈ E <;> simp [halfPrior,hd]
    ring
  have hi : Integrable (fun d => (1/2 : ℝ)*E.indicator (fun x => f₁ x-f₀ x) d) μ :=
    ((h₁.sub h₀).indicator hE).const_mul _
  rw [he,integral_add h₀ hi,
    integral_const_mul,integral_indicator hE]

theorem population_halfPrior_moment {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (E : Set D) (hE : MeasurableSet E) :
    (populationSecondMoment μ ν p₀ p₁ (halfPrior E) A).toReal =
      (populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal +
      (1/2)*(∫ d in E, (conditionalSecondMoment ν (p₁ d) A).toReal -
        (conditionalSecondMoment ν (p₀ d) A).toReal ∂μ) := by
  obtain ⟨hi₀,hi₁,_⟩ := conditional_moment_pair_integrable μ ν p₀ p₁ h₀ h₁ c hc A hm₀ hm₁
  rw [population_second_moment_real_formula μ ν p₀ p₁ h₀ h₁ c hc A hm₀ hm₁ _
    (measurable_halfPrior E hE),halfPrior_weighted_integral μ E hE _ _ hi₀ hi₁]
  have he := population_second_moment_real_formula μ ν p₀ p₁ h₀ h₁ c hc A hm₀ hm₁
    (fun _ => 0) measurable_const
  norm_num at he
  rw [he]

theorem population_halfPrior_mean {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (E : Set D) (hE : MeasurableSet E) :
    populationMean μ ν p₀ p₁ (halfPrior E) A =
      populationMean μ ν p₀ p₁ (fun _ => 0) A +
      (1/2)*(∫ d in E, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ∂μ) := by
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  have hi := population_finite_components μ ν p₀ p₁ h₀ h₁ c hc _ hsq hm₀ hm₁
  have hi₀ := conditionalMean_integrable_of_moment μ ν p₀ h₀ A hi.1
  have hi₁ := conditionalMean_integrable_of_moment μ ν p₁ h₁ A hi.2
  have hfin := population_finite_all μ ν p₀ p₁ h₀ h₁ c hc _ hsq hm₀ hm₁ _
    (measurable_halfPrior E hE)
  rw [population_mean_formula μ ν p₀ p₁ _ h₀ h₁ (measurable_halfPrior E hE) A hfin,
    halfPrior_weighted_integral μ E hE _ _ hi₀ hi₁]
  have he := population_mean_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A hm₀
  norm_num at he
  rw [he]

end ThresholdHC.CriticalEntropy
