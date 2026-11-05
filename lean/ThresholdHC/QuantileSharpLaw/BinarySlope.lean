import ThresholdHC.EntropyTailQuantile.CostEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

noncomputable section
open Real
namespace ThresholdHC.QuantileSharpLaw

theorem exp_difference_lower {x : ℝ} (hx : 0 ≤ x) :
    x+x^2 ≤ exp x-exp (-x) := by
  have h := (hasSum_sinh x).summable.sum_le_tsum (Finset.range 2)
    (fun n _ => div_nonneg (pow_nonneg hx _) (by positivity))
  rw [(hasSum_sinh x).tsum_eq] at h
  norm_num [Finset.sum_range_succ,Real.sinh_eq] at h
  have hp := mul_nonneg hx (sq_nonneg (x-3/2))
  nlinarith only [h,hp,hx]

theorem binary_entropy_slope_bound {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    p*(1-log p)^2 ≤ 1+binEntropy p := by
  rcases hp1.eq_or_lt with rfl | hp1
  · simp
  have hl : 0 ≤ -log p := neg_nonneg.mpr (log_nonpos hp.le hp1.le)
  have he := mul_le_mul_of_nonneg_left (exp_difference_lower hl) hp.le
  have hid : p*(exp (-log p)-exp (-(-log p))) = 1-p^2 := by
    rw [neg_neg,exp_neg,exp_log hp,mul_sub,mul_inv_cancel₀ hp.ne']
    ring
  rw [hid] at he
  have ht := log_le_sub_one_of_pos (show 0 < 1-p by linarith)
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 1-p by linarith)
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold negMulLog
  nlinarith only [he,hm]

end ThresholdHC.QuantileSharpLaw
