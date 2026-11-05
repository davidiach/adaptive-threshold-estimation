import ThresholdHC.OptimalQuantile.Finite

noncomputable section
open Real
namespace ThresholdHC.OptimalQuantile

theorem dualPrice_ge_two {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u) :
    2 ≤ dualPrice k u := by
  have hs1 : 1 ≤ sqrt (2 : ℝ) := one_le_sqrt.mpr (by norm_num)
  have hs3 : sqrt (2 : ℝ) ≤ 3/2 := sqrt_le_iff.mpr (by norm_num)
  have hs2 : (sqrt (2 : ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have hp : 0 ≤ (k-sqrt 2)*(k+sqrt 2-1) :=
    mul_nonneg (sub_nonneg.mpr hk) (by linarith)
  have ht := sqrt_tangent (a := 0) (by norm_num) (show 0 < u by linarith)
  norm_num only [add_zero,sqrt_one] at ht
  have hA : 2 ≤ u+1/u := by linarith
  have hm := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2*k^2 by positivity)
  unfold dualPrice
  nlinarith only [hp,hs2,hs3,hm]

theorem first_exponent_identity (k : ℝ) {u : ℝ} (hu : u ≠ 0) :
    1-dualPrice k u/(2*u) = 2-k^2-(k/u-1)^2 := by
  unfold dualPrice
  field_simp [hu]
  ring

end ThresholdHC.OptimalQuantile
