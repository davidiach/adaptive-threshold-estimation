import ThresholdHC.OptimalQuantile.Gibbs

noncomputable section
open Real
namespace ThresholdHC.OptimalQuantile

theorem sqrt_tangent {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    sqrt (1+a) ≤ (u+(1+a)/u)/2 := by
  have hs : (sqrt (1+a))^2 = 1+a := sq_sqrt (by linarith)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h : 2*sqrt (1+a)-u ≤ (1+a)/u := by
    apply (le_div_iff₀ hu).mpr
    nlinarith only [sq_nonneg (u-sqrt (1+a)),hs]
  linarith

theorem sqrt_tangent_attained {a : ℝ} (ha : 0 ≤ a) :
    ∃ u : ℝ, 1 ≤ u ∧ sqrt (1+a) = (u+(1+a)/u)/2 := by
  let u := sqrt (1+a)
  have hu : 1 ≤ u := one_le_sqrt.mpr (by linarith)
  have hu0 : u ≠ 0 := ne_of_gt (by linarith : 0 < u)
  have hu2 : u^2 = 1+a := sq_sqrt (by linarith)
  refine ⟨u,hu,?_⟩
  change u = (u+(1+a)/u)/2
  rw [← hu2,pow_two,mul_div_cancel_right₀ _ hu0]
  ring

theorem price_iff_all_tangents {a c g k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) :
    (1+sqrt g ≤ k*(sqrt (1+a)+c)) ↔
      ∀ u : ℝ, 1 ≤ u → 1+sqrt g ≤ k*((u+(1+a)/u)/2+c) := by
  constructor
  · intro h u hu
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (sqrt_tangent ha (by linarith)) (le_refl c)) hk)
  · intro h
    obtain ⟨u,hu,he⟩ := sqrt_tangent_attained ha
    rw [he]
    exact h u hu

end ThresholdHC.OptimalQuantile
