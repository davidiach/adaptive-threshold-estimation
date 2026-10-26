import ThresholdHC.Uniform713.Estimator

/-!
Integration of conditional moment bounds over arbitrary parameter laws.
The hypotheses are intermediate analytic interfaces: the final model theorem
must obtain them from its actual classifier and observation kernel.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ThresholdHC.Uniform713

/-- Integrate a nonnegative conditional moment bounded by an integrable envelope. -/
theorem integrate_conditional_bound
    {Θ A : Type*} [MeasurableSpace Θ] [MeasurableSpace A]
    {ν : Measure Θ} [SFinite ν] {K : Kernel Θ A} [IsSFiniteKernel K]
    {F : Θ × A → ℝ} {g : Θ → ℝ}
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hi : ∀ᵐ θ ∂ν, Integrable (fun a => F (θ,a)) (K θ))
    (hg : Integrable g ν)
    (hb : ∀ᵐ θ ∂ν, (∫ a, F (θ,a) ∂K θ) ≤ g θ) :
    Integrable F (ν ⊗ₘ K) ∧ (∫ x, F x ∂(ν ⊗ₘ K)) ≤ ∫ θ, g θ ∂ν := by
  have hinner : Integrable (fun θ => ∫ a, F (θ,a) ∂K θ) ν := by
    apply hg.mono' hF.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [hb] with θ hθ
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun a => hF0 (θ,a)))] using hθ
  have hint : Integrable F (ν ⊗ₘ K) := by
    apply (Measure.integrable_compProd_iff hF.aestronglyMeasurable).2
    refine ⟨hi, ?_⟩
    simpa only [Real.norm_of_nonneg (hF0 _)] using hinner
  refine ⟨hint, ?_⟩
  rw [Measure.integral_compProd hint]
  exact integral_mono_ae hinner hg hb

/-- The inverse-gap envelope used for both the second moment and expected work. -/
theorem integrate_conditional_inverse_gap
    {Θ A : Type*} [MeasurableSpace Θ] [MeasurableSpace A]
    {ν : Measure Θ} [SFinite ν] {K : Kernel Θ A} [IsSFiniteKernel K]
    {F : Θ × A → ℝ} {d : Θ → ℝ} {C : ℝ}
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hi : ∀ᵐ θ ∂ν, Integrable (fun a => F (θ,a)) (K θ))
    (hd : Integrable (fun θ => (d θ)⁻¹) ν)
    (hb : ∀ᵐ θ ∂ν, (∫ a, F (θ,a) ∂K θ) ≤ C / d θ) :
    Integrable F (ν ⊗ₘ K) ∧
      (∫ x, F x ∂(ν ⊗ₘ K)) ≤ C * ∫ θ, (d θ)⁻¹ ∂ν := by
  simpa only [div_eq_mul_inv, integral_const_mul] using
    integrate_conditional_bound hF hF0 hi (hd.const_mul C) hb

theorem integrate_conditional_strict_bound
    {Θ A : Type*} [MeasurableSpace Θ] [MeasurableSpace A]
    {ν : Measure Θ} [IsProbabilityMeasure ν] {K : Kernel Θ A} [IsSFiniteKernel K]
    {F : Θ × A → ℝ} {g : Θ → ℝ}
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hi : ∀ᵐ θ ∂ν, Integrable (fun a => F (θ,a)) (K θ))
    (hg : Integrable g ν)
    (hb : ∀ᵐ θ ∂ν, (∫ a, F (θ,a) ∂K θ) < g θ) :
    Integrable F (ν ⊗ₘ K) ∧ (∫ x, F x ∂(ν ⊗ₘ K)) < ∫ θ, g θ ∂ν := by
  have hble := hb.mono (fun _ h => h.le)
  obtain ⟨hint, hle⟩ := integrate_conditional_bound hF hF0 hi hg hble
  have hinner : Integrable (fun θ => ∫ a, F (θ,a) ∂K θ) ν := by
    apply hg.mono' hF.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [hble] with θ hθ
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun a => hF0 (θ,a)))] using hθ
  refine ⟨hint, lt_of_le_of_ne hle ?_⟩
  intro heq
  rw [Measure.integral_compProd hint] at heq
  have heqae := (integral_eq_iff_of_ae_le hinner hg hble).1 heq
  obtain ⟨θ, hlt, he⟩ := (hb.and heqae).exists
  exact (ne_of_lt hlt) he

theorem integrate_conditional_inverse_gap_strict
    {Θ A : Type*} [MeasurableSpace Θ] [MeasurableSpace A]
    {ν : Measure Θ} [IsProbabilityMeasure ν] {K : Kernel Θ A} [IsSFiniteKernel K]
    {F : Θ × A → ℝ} {d : Θ → ℝ} {C : ℝ}
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hi : ∀ᵐ θ ∂ν, Integrable (fun a => F (θ,a)) (K θ))
    (hd : Integrable (fun θ => (d θ)⁻¹) ν)
    (hb : ∀ᵐ θ ∂ν, (∫ a, F (θ,a) ∂K θ) < C / d θ) :
    Integrable F (ν ⊗ₘ K) ∧
      (∫ x, F x ∂(ν ⊗ₘ K)) < C * ∫ θ, (d θ)⁻¹ ∂ν := by
  simpa only [div_eq_mul_inv, integral_const_mul] using
    integrate_conditional_strict_bound hF hF0 hi (hd.const_mul C) hb

/-- The final variance-work comparison, after both moment bounds have been established. -/
theorem variance_work_lt_713
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {Y W : A → ℝ} {I : ℝ}
    (hY : MemLp Y 2 μ) (hW0 : ∀ a, 0 ≤ W a) (hI : 0 < I)
    (hYb : (∫ a, Y a ^ 2 ∂μ) < 23 * I)
    (hWb : (∫ a, W a ∂μ) ≤ 31 * I) :
    variance Y μ * (∫ a, W a ∂μ) < 713 * I ^ 2 := by
  calc
    variance Y μ * (∫ a, W a ∂μ) ≤ (∫ a, Y a ^ 2 ∂μ) * (∫ a, W a ∂μ) :=
      mul_le_mul_of_nonneg_right (variance_le_expectation_sq hY.aestronglyMeasurable)
        (integral_nonneg hW0)
    _ ≤ (∫ a, Y a ^ 2 ∂μ) * (31 * I) :=
      mul_le_mul_of_nonneg_left hWb (integral_nonneg (fun _ => sq_nonneg _))
    _ < (23 * I) * (31 * I) := mul_lt_mul_of_pos_right hYb (by positivity)
    _ = 713 * I ^ 2 := by ring

end ThresholdHC.Uniform713
