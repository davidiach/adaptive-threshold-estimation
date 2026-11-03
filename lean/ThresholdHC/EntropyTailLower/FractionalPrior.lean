import ThresholdHC.CriticalEntropy.HalfPrior

/-! Fractional event priors retain atoms. They spend exactly the requested
global rarity mass without selecting a subset of prescribed measure. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

def eventPrior {D : Type} (E : Set D) (c : unitInterval) (d : D) : unitInterval := by
  classical
  exact if d ∈ E then c else 0

theorem measurable_eventPrior {D : Type} [MeasurableSpace D] (E : Set D)
    (hE : MeasurableSet E) (c : unitInterval) : Measurable (eventPrior E c) := by
  unfold eventPrior
  exact Measurable.ite hE measurable_const measurable_const

theorem eventPrior_integral {D : Type} [MeasurableSpace D]
    (μ : Measure D) (E : Set D) (hE : MeasurableSet E) (c : unitInterval) :
    (∫ d, (eventPrior E c d : ℝ) ∂μ) = (c:ℝ)*μ.real E := by
  have he : (fun d => (eventPrior E c d : ℝ)) = E.indicator (fun _ => (c:ℝ)) := by
    funext d
    by_cases hd : d ∈ E <;> simp [eventPrior,hd]
  rw [he,integral_indicator hE,setIntegral_const]
  simp [smul_eq_mul,mul_comm]

theorem cappedPrior_event {D : Type} [MeasurableSpace D]
    (μ : Measure D) (ρ : ℝ) (E : Set D) (hE : MeasurableSet E)
    (c : unitInterval) (hc : (c:ℝ) ≤ 1/2) (hm : (c:ℝ)*μ.real E ≤ ρ) :
    CappedPrior μ ρ (eventPrior E c) := by
  refine ⟨measurable_eventPrior E hE c,?_,?_⟩
  · intro d
    by_cases hd : d ∈ E
    · simpa only [eventPrior,ite_eq_left hd] using hc
    · simp [eventPrior,hd]
  · rwa [eventPrior_integral μ E hE c]

theorem exists_fractional_mass {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsFiniteMeasure μ] (E : Set D) (ρ : ℝ)
    (hρ : 0 < ρ) (hE : 2*ρ ≤ μ.real E) :
    ∃ c : unitInterval, 0 < (c:ℝ) ∧ (c:ℝ) ≤ 1/2 ∧ (c:ℝ)*μ.real E = ρ := by
  have hm : 0 < μ.real E := by linarith
  have hc : ρ/μ.real E ≤ 1/2 := (div_le_iff₀ hm).mpr (by linarith)
  refine ⟨⟨ρ/μ.real E,⟨by positivity,by linarith⟩⟩,by dsimp; positivity,hc,?_⟩
  dsimp
  exact div_mul_cancel₀ ρ hm.ne'

theorem eventPrior_weighted_integral {D : Type} [MeasurableSpace D]
    (μ : Measure D) (E : Set D) (hE : MeasurableSet E) (c : unitInterval)
    (f₀ f₁ : D → ℝ) (h₀ : Integrable f₀ μ) (h₁ : Integrable f₁ μ) :
    (∫ d, (eventPrior E c d : ℝ)*f₁ d+(1-(eventPrior E c d : ℝ))*f₀ d ∂μ) =
      (∫ d, f₀ d ∂μ)+(c:ℝ)*(∫ d in E, f₁ d-f₀ d ∂μ) := by
  have he : (fun d => (eventPrior E c d : ℝ)*f₁ d+(1-(eventPrior E c d : ℝ))*f₀ d) =
      fun d => f₀ d+(c:ℝ)*E.indicator (fun x => f₁ x-f₀ x) d := by
    funext d
    by_cases hd : d ∈ E <;> simp [eventPrior,hd]; ring
  have hi : Integrable (fun d => (c:ℝ)*E.indicator (fun x => f₁ x-f₀ x) d) μ :=
    ((h₁.sub h₀).indicator hE).const_mul _
  rw [he,integral_add h₀ hi,
    integral_const_mul,integral_indicator hE]

theorem population_eventPrior_moment {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (r : unitInterval) (hr : 0 < (r:ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => r) A ≠ ∞)
    (E : Set D) (hE : MeasurableSet E) (c : unitInterval) :
    (populationSecondMoment μ ν p₀ p₁ (eventPrior E c) A).toReal =
      (populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal +
      (c:ℝ)*(∫ d in E, (conditionalSecondMoment ν (p₁ d) A).toReal -
        (conditionalSecondMoment ν (p₀ d) A).toReal ∂μ) := by
  obtain ⟨hi₀,hi₁,_⟩ := conditional_moment_pair_integrable μ ν p₀ p₁ h₀ h₁ r hr A hm₀ hm₁
  rw [population_second_moment_real_formula μ ν p₀ p₁ h₀ h₁ r hr A hm₀ hm₁ _
    (measurable_eventPrior E hE c),eventPrior_weighted_integral μ E hE c _ _ hi₀ hi₁]
  have he := population_second_moment_real_formula μ ν p₀ p₁ h₀ h₁ r hr A hm₀ hm₁
    (fun _ => 0) measurable_const
  norm_num at he
  rw [he]

theorem population_eventPrior_mean {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (r : unitInterval) (hr : 0 < (r:ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => r) A ≠ ∞)
    (E : Set D) (hE : MeasurableSet E) (c : unitInterval) :
    populationMean μ ν p₀ p₁ (eventPrior E c) A =
      populationMean μ ν p₀ p₁ (fun _ => 0) A +
      (c:ℝ)*(∫ d in E, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ∂μ) := by
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  have hi := population_finite_components μ ν p₀ p₁ h₀ h₁ r hr _ hsq hm₀ hm₁
  have hi₀ := conditionalMean_integrable_of_moment μ ν p₀ h₀ A hi.1
  have hi₁ := conditionalMean_integrable_of_moment μ ν p₁ h₁ A hi.2
  have hfin := population_finite_all μ ν p₀ p₁ h₀ h₁ r hr _ hsq hm₀ hm₁ _
    (measurable_eventPrior E hE c)
  rw [population_mean_formula μ ν p₀ p₁ _ h₀ h₁ (measurable_eventPrior E hE c) A hfin,
    eventPrior_weighted_integral μ E hE c _ _ hi₀ hi₁]
  have he := population_mean_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A hm₀
  norm_num at he
  rw [he]

end ThresholdHC.EntropyTailLower
