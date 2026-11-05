import ThresholdHC.ShiftedPower.Kernels
import ThresholdHC.Uniform713.Common

noncomputable section
open Real
namespace ThresholdHC.ShiftedPower

/-- A fractional power uniformly controls the logarithmic stopping cost.
The exponent may be chosen between half the margin exponent and one. -/
theorem log_work_bound {n d r : ℝ} (hn : 0 < n) (hd : 0 < d) (hr : 0 ≤ r) (hr' : r < 1) :
    min n (d⁻¹^2*(1+max 0 (Real.log (n*d^2)))) ≤
      (1/(1-r))*n*min 1 (((Real.sqrt n)⁻¹/d)^(2*r)) := by
  let t := n*d^2
  have ht : 0 < t := mul_pos hn (sq_pos_of_pos hd)
  have hu : 0 < 1-r := by linarith
  have hc : 1 ≤ 1/(1-r) := (one_le_div hu).mpr (by linarith)
  have hsq : ((Real.sqrt n)⁻¹/d)^2 = t⁻¹ := by
    dsimp [t]
    rw [div_pow,inv_pow,Real.sq_sqrt hn.le]
    field_simp
  have he : ((Real.sqrt n)⁻¹/d)^(2*r) = t^(-r) := by
    rw [Real.rpow_mul (by positivity : 0 ≤ (Real.sqrt n)⁻¹/d),Real.rpow_two,hsq,
      Real.inv_rpow ht.le,Real.rpow_neg ht.le]
  rw [he]
  by_cases ht1 : t ≤ 1
  · have hp : 1 ≤ t^(-r) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (neg_nonpos.mpr hr)
    rw [min_eq_left hp,mul_one]
    exact (min_le_left _ _).trans (le_mul_of_one_le_left hn.le hc)
  · have ht1' : 1 ≤ t := (le_of_not_ge ht1)
    have hp : t^(-r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1' (neg_nonpos.mpr hr)
    rw [min_eq_right hp]
    apply (min_le_right _ _).trans
    rw [max_eq_right (Real.log_nonneg ht1')]
    have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht (1-r))
    rw [Real.log_rpow ht] at hl
    have hpow : (1-r)*(1+Real.log t) ≤ t^(1-r) := by nlinarith only [hl,hr]
    have hid : d⁻¹^2 = n/t := by dsimp [t]; field_simp
    rw [hid]
    have he' : t^(1-r) = t*t^(-r) := by
      rw [sub_eq_add_neg,Real.rpow_add ht,Real.rpow_one]
    rw [he'] at hpow
    change n/t*(1+Real.log t) ≤ (1/(1-r))*n*t^(-r)
    have hlog : 1+Real.log t ≤ (t*t^(-r))/(1-r) :=
      (le_div_iff₀ hu).mpr (by nlinarith only [hpow])
    calc n/t*(1+Real.log t) ≤ n/t*((t*t^(-r))/(1-r)) :=
           mul_le_mul_of_nonneg_left hlog (div_nonneg hn.le ht.le)
         _ = _ := by field_simp

end ThresholdHC.ShiftedPower
