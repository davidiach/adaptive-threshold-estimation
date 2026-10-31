import ThresholdHC.StoppingProgram.FourPriorMultipliers

/-! Eliminating the free offset, bias and variance coordinates leaves the
actual nonnegative conic work-price functional and its attained objective. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap signMean)

theorem linear_lower_bound_forces_zero {p t d : ℝ} (h : ∀ r : ℝ, p ≤ t+r*d) : d = 0 := by
  by_contra hd
  have hh := h ((p-t-1)/d)
  rw [div_mul_cancel₀ _ hd] at hh
  linarith

theorem linear_ray_lower_bound_forces_nonneg {p t d : ℝ}
    (h : ∀ r : ℝ, 0 ≤ r → p ≤ t+r*d) : 0 ≤ d := by
  by_contra hd
  have hd' : d < 0 := lt_of_not_ge hd
  have h0 := h 0 le_rfl
  simp only [zero_mul,add_zero] at h0
  let r := (t-p+1)/(-d)
  have hr : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hh := h r hr
  have he : r*d = -(t-p+1) := by dsimp [r]; field_simp [ne_of_lt hd']
  rw [he] at hh
  linarith

def conePrice {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (α η : ℝ) (f : Flow N) : ℝ :=
  countMean μ Q.variance f.momentWeight-
    α*(countMean μ Q.high f.outputWeight-countMean μ Q.low f.outputWeight)+
    η*countMean μ Q.work f.continueWeight

theorem attained_price_multipliers (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) :
    ∃ (Q : FourPriors) (α η : ℝ), Admissible μ ρ Q ∧ 0 ≤ α ∧ 0 ≤ η ∧
      (programSquared μ ρ B N).toReal ≤
        α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B ∧
      ∀ f : Flow N, FlowCone f → 0 ≤ conePrice μ Q α η f := by
  obtain ⟨w,Q,hw,hQ,h⟩ := four_prior_multipliers N μ hρ hB
  have hfree (r : ℝ) := h ⟨zeroFlow N,r,0,0⟩ (zeroFlow_cone N) le_rfl le_rfl
  simp only [zeroFlow,countMean,mul_zero,Finset.sum_const_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
    zero_add,add_zero,sub_zero,zero_sub] at hfree
  have hw01 : w 0 = w 1 := by
    have hh : w 0-w 1 = 0 := linear_lower_bound_forces_zero
      (p := (programSquared μ ρ B N).toReal)
      (t := w 1*signMean μ Q.high.val-w 0*signMean μ Q.low.val-w 3*B)
      (fun r => by have ht := hfree r; nlinarith)
    linarith
  have hvar : w 2 ≤ 1 := by
    have hh : 0 ≤ 1-w 2 := linear_ray_lower_bound_forces_nonneg
      (p := (programSquared μ ρ B N).toReal)
      (t := w 1*(signMean μ Q.high.val-signMean μ Q.low.val)-w 3*B) (by
        intro r hr
        have ht := h ⟨zeroFlow N,0,0,r⟩ (zeroFlow_cone N) le_rfl hr
        simp only [zeroFlow,countMean,mul_zero,Finset.sum_const_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
          zero_add,add_zero,sub_zero,zero_sub,hw01] at ht
        nlinarith)
    linarith
  refine ⟨Q,w 1,w 3,hQ,hw 1,hw 3,?_,?_⟩
  · have ht := h ⟨zeroFlow N,0,w 1,0⟩ (zeroFlow_cone N) (hw 1) le_rfl
    simp only [zeroFlow,countMean,mul_zero,Finset.sum_const_zero,add_zero,sub_zero,zero_sub,hw01] at ht
    nlinarith
  · intro f hf
    have hh : 0 ≤ w 2*countMean μ Q.variance f.momentWeight-
        w 1*(countMean μ Q.high f.outputWeight-countMean μ Q.low f.outputWeight)+
        w 3*countMean μ Q.work f.continueWeight := linear_ray_lower_bound_forces_nonneg
      (p := (programSquared μ ρ B N).toReal)
      (t := w 1*(signMean μ Q.high.val-signMean μ Q.low.val)-w 3*B) (by
        intro r hr
        have ht := h ⟨scaleFlow r f,0,0,0⟩ (hf.scale hr) le_rfl le_rfl
        simp only [scaleFlow,countMean_scale,zero_pow (by decide : (2:ℕ) ≠ 0),
          zero_add,add_zero,sub_zero,hw01] at ht
        nlinarith)
    have hm := countMean_nonneg μ Q.variance f.momentWeight hf.moment_nonneg
    dsimp only [conePrice]
    nlinarith [mul_nonneg (sub_nonneg.mpr hvar) hm]

end ThresholdHC.StoppingProgram
