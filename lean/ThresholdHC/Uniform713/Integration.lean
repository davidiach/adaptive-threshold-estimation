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

end ThresholdHC.Uniform713
