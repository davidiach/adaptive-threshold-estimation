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

private lemma exp_step_v1 (t : ℝ) :
    t * Real.exp (-t) ≤ 2 * (Real.exp (-(t/2)) - Real.exp (-t)) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t/2))
    (Real.exp_pos (-t)).le
  have heq : Real.exp (t/2) * Real.exp (-t) = Real.exp (-(t/2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  nlinarith only [h]

theorem dyadic_sum_v1 : ThresholdHC.Targets.dyadic_sum_v1 := by
  intro b hb
  have hpartial : ∀ m : ℕ,
      b * (∑ k ∈ Finset.range m, (2:ℝ)^k * Real.exp (-(b*2^k)))
      ≤ 2 * (Real.exp (-(b/2)) - Real.exp (-(b*2^m/2))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hpow : b * (2:ℝ)^(m+1) / 2 = b * 2^m := by rw [pow_succ]; ring
      rw [hpow]
      have hs := exp_step_v1 (b * (2:ℝ)^m)
      nlinarith only [ih, hs]
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro m
  apply (le_div_iff₀ hb).2
  have hs := hpartial m
  have hstart : Real.exp (-(b/2)) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -(b/2) ≤ 0 by linarith)
  have hend := (Real.exp_pos (-(b*(2:ℝ)^m/2))).le
  nlinarith only [hs, hstart, hend]

private noncomputable def expTail (t : ℝ) := (1+t) * Real.exp (-t)

private lemma expTail_le_one (t : ℝ) : expTail t ≤ 1 := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
  rw [← Real.exp_add] at h
  simpa [expTail, add_comm] using h

private lemma exp_step_v2 (t : ℝ) (ht : 0 ≤ t) :
    t^2 * Real.exp (-t) ≤ (8/3:ℝ) * (expTail (t/2) - expTail t) := by
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ t/2 by linarith)
  have h := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ (1+t/2) * Real.exp (-t) by positivity)
  have heq : Real.exp (t/2) * ((1+t/2) * Real.exp (-t)) = expTail (t/2) := by
    calc
      _ = (1+t/2) * (Real.exp (t/2) * Real.exp (-t)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        unfold expTail
        congr 2
        ring
  rw [heq] at h
  have hcub : 0 ≤ t^3 * Real.exp (-t) := by positivity
  dsimp [expTail] at h ⊢
  nlinarith only [h, hcub]

theorem dyadic_sum_v2 : ThresholdHC.Targets.dyadic_sum_v2 := by
  intro b hb
  have hpartial : ∀ m : ℕ,
      b^2 * (∑ k ∈ Finset.range m, ((2:ℝ)^k)^2 * Real.exp (-(b*2^k)))
      ≤ (8/3:ℝ) * (expTail (b/2) - expTail (b*2^m/2)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hpow : b * (2:ℝ)^(m+1) / 2 = b * 2^m := by rw [pow_succ]; ring
      rw [hpow]
      have hs := exp_step_v2 (b * (2:ℝ)^m) (by positivity)
      nlinarith only [ih, hs]
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro m
  apply (le_div_iff₀ (show 0 < 3 * b^2 by positivity)).2
  have hs := hpartial m
  have hstart := expTail_le_one (b/2)
  have hend : 0 ≤ expTail (b*(2:ℝ)^m/2) := by unfold expTail; positivity
  nlinarith only [hs, hstart, hend]

end ThresholdHC.Proofs
