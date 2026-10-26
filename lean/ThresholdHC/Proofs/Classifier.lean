import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

theorem error_tail_bound : ThresholdHC.Targets.error_tail_bound := by
  intro x hx
  have hxpos : 0 < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hexp : x ≤ Real.exp (x-1) := by linarith [Real.add_one_le_exp (x-1)]
  have hxsq : x^2 ≤ (Real.exp (x-1))^2 := by nlinarith [Real.exp_pos (x-1)]
  have hprod := mul_le_mul_of_nonneg_right hxsq (le_of_lt (Real.exp_pos (-2*x)))
  have heq : (Real.exp (x-1))^2 * Real.exp (-2*x) = Real.exp (-2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hprod
  have hsmall : Real.exp (-2) ≤ (1/3 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos 2)).2
    linarith [Real.add_one_le_exp (2 : ℝ)]
  apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hxpos)).mp
  calc
    (Real.exp (-2*x) + Real.exp (-2) * (2/3) * (x⁻¹)^2) * x^2 =
        x^2 * Real.exp (-2*x) + (2/3) * Real.exp (-2) := by field_simp <;> ring
    _ ≤ (5/3) * Real.exp (-2) := by linarith
    _ < 1 := by linarith
    _ = (x⁻¹)^2 * x^2 := by field_simp

theorem classifier_scale_step : ThresholdHC.Targets.classifier_scale_step := by
  intro n N d hn hnN hd hNd hstop
  have hN : 0 < N := lt_of_lt_of_le hn hnN
  have hlog : 0 ≤ Real.log (N * d ^ 2) := Real.log_nonneg hNd
  by_cases hsmall : n * d ^ 2 ≤ 4
  · linarith
  have hnd : 1 ≤ n * d ^ 2 := by linarith
  have hratio : N / n ≤ N * d ^ 2 := by
    apply (div_le_iff₀ hn).2
    nlinarith [mul_le_mul_of_nonneg_left hnd (le_of_lt hN)]
  have hlogratio : Real.log (N / n) ≤ Real.log (N * d ^ 2) :=
    Real.log_le_log (div_pos hN hn) hratio
  have hNn : 1 ≤ N / n := (one_le_div hn).2 hnN
  have hbase : 0 ≤ (1 + Real.log (N / n)) / n := by
    have := Real.log_nonneg hNn
    positivity
  have hsqrt := Real.sq_sqrt hbase
  have hsqrtnonneg := Real.sqrt_nonneg ((1 + Real.log (N / n)) / n)
  have hsquared : d ^ 2 ≤ 4 * ((1 + Real.log (N / n)) / n) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsquared (le_of_lt hn)
  have heq : n * (4 * ((1 + Real.log (N / n)) / n)) = 4 * (1 + Real.log (N / n)) := by
    field_simp
  rw [heq] at hscaled
  linarith

theorem dyadic_sum_v1 : ThresholdHC.Targets.dyadic_sum_v1 := by
  sorry

theorem dyadic_sum_v2 : ThresholdHC.Targets.dyadic_sum_v2 := by
  sorry

end ThresholdHC.Proofs
