import ThresholdHC.OptimalQuantile.Maximum
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.OptimalQuantile

theorem exp_three_lt_twentyfive : exp (3 : ℝ) < 25 := by
  have h1 : exp (1 : ℝ) < 11/4 := lt_trans exp_one_lt_d9 (by norm_num)
  have h3 := pow_lt_pow_left₀ h1 (exp_pos 1).le (by norm_num : (3 : ℕ) ≠ 0)
  have he : exp (3 : ℝ) = (exp 1)^3 := by
    simp [← exp_nat_mul]
  rw [he]
  nlinarith only [h3]

theorem exp_seven_fifths_lt_five : exp (7/5 : ℝ) < 5 := by
  have he : (exp (3/2 : ℝ))^2 = exp 3 := by
    rw [pow_two,← exp_add]
    norm_num
  have h : exp (3/2 : ℝ) < 5 := by
    have hp := exp_pos (3/2 : ℝ)
    nlinarith only [he,exp_three_lt_twentyfive,hp]
  exact (exp_lt_exp.mpr (by norm_num : (7/5 : ℝ) < 3/2)).trans h

theorem scalarPeak_lower_endpoint : 1 < scalarPeak (sqrt 2) := by
  have hs : (7/5 : ℝ) ≤ sqrt 2 := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hs2 : (sqrt (2 : ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have hp : dualPrice (sqrt 2) 1 ≤ 12/5 := by
    unfold dualPrice
    norm_num
    nlinarith only [hs,hs2]
  have hf : (4/5 : ℝ) ≤ exp (1-dualPrice (sqrt 2) 1/(2*1)) := by
    have he := add_one_le_exp (-1/5 : ℝ)
    have hm := exp_le_exp.mpr (show (-1/5 : ℝ) ≤ 1-dualPrice (sqrt 2) 1/(2*1) by linarith)
    linarith
  have hg : (1/5 : ℝ) < exp (1-dualPrice (sqrt 2) 1) := by
    have hi : (1/5 : ℝ) < exp (-7/5 : ℝ) := by
      rw [show (-7/5 : ℝ) = -(7/5) by ring,exp_neg]
      simpa only [one_div] using
        (one_div_lt_one_div_of_lt (exp_pos _) exp_seven_fifths_lt_five)
    exact hi.trans_le (exp_le_exp.mpr (by linarith))
  have ht : exp (1-dualPrice (sqrt 2) 1) ≤ exponentialTail (dualPrice (sqrt 2) 1) := by
    have h := (exponentialTail_summable
      (dualPrice_ge_two (k := sqrt 2) (u := 1) le_rfl (by norm_num))).le_tsum
      0 (fun j _ => (exp_pos _).le)
    simpa [exponentialTail] using h
  have hpoint : 1 < partitionSeries (sqrt 2) 1 := by
    unfold partitionSeries
    linarith
  exact hpoint.trans_le (partitionSeries_le_peak le_rfl (by norm_num))

theorem exponentialTail_bound_three {price : ℝ} (hp : 3 ≤ price) :
    exponentialTail price ≤ exp (-2)/(1-exp (-3)) := by
  have hg : Summable (fun n : ℕ => (exp (-3))^n) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      exact exp_lt_one_iff.mpr (by norm_num))
  have hbound (n : ℕ) : exp (1-price*(2 : ℝ)^n) ≤ exp (-2)*(exp (-3))^n := by
    calc
      _ ≤ exp (-2+(n : ℝ)*(-3)) := by
        apply exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ (2 : ℝ)^n by positivity)
        nlinarith only [hm,power_two_lower n]
      _ = _ := by rw [exp_add,exp_nat_mul]
  have h := Summable.tsum_le_tsum hbound (exponentialTail_summable (by linarith)) (hg.mul_left _)
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one] at h
  · simpa [exponentialTail,div_eq_mul_inv] using h
  · rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.mpr (by norm_num)

theorem exp_two_gt_five : (5 : ℝ) < exp 2 := by
  have h : (5/2 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have he : exp (2 : ℝ) = (exp 1)^2 := by simp [← exp_nat_mul]
  rw [he]
  nlinarith only [h]

theorem scalarPeak_upper_endpoint : scalarPeak (31/20) < 1 := by
  have hk : sqrt (2 : ℝ) ≤ 31/20 := sqrt_le_iff.mpr (by norm_num)
  obtain ⟨u,hu,he,_⟩ := scalarPeak_attained hk
  rw [he]
  have hp : 3 ≤ dualPrice (31/20) u := by
    have ht := sqrt_tangent (a := 0) (by norm_num) (show 0 < u by linarith [hu.1])
    norm_num only [add_zero,sqrt_one] at ht
    unfold dualPrice
    nlinarith only [ht]
  have hf : exp (1-dualPrice (31/20) u/(2*u)) < 3/4 := by
    rw [first_exponent_identity _ (show u ≠ 0 by linarith [hu.1])]
    have hexp : (4/3 : ℝ) < exp (1/3) := by
      have h := add_one_lt_exp (by norm_num : (1/3 : ℝ) ≠ 0)
      linarith
    have hi : exp (-1/3 : ℝ) < 3/4 := by
      rw [show (-1/3 : ℝ) = -(1/3) by ring,exp_neg]
      have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4/3) hexp
      norm_num at h ⊢
      exact h
    have harg : 2-(31/20 : ℝ)^2-((31/20)/u-1)^2 ≤ -1/3 := by
      nlinarith only [sq_nonneg ((31/20)/u-1)]
    exact (exp_le_exp.mpr harg).trans_lt hi
  have h2 : exp (-2 : ℝ) < 1/5 := by
    rw [exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num) exp_two_gt_five
  have h3 : exp (-3 : ℝ) < 1/5 := by
    exact (exp_lt_exp.mpr (by norm_num : (-3 : ℝ) < -2)).trans h2
  have hd : 0 < 1-exp (-3 : ℝ) := by linarith
  have ht := exponentialTail_bound_three hp
  have ht' : exp (-2 : ℝ)/(1-exp (-3)) < 1/4 := by
    apply (div_lt_iff₀ hd).mpr
    linarith
  unfold partitionSeries
  linarith

end ThresholdHC.OptimalQuantile
