import ThresholdHC.Uniform713.Common

/-! Deterministic estimates used to bound the classifier's expected work. -/

noncomputable section

namespace ThresholdHC.Uniform713

open Real MeasureTheory

theorem survival_indicator_scale_step (n N d : ℝ) (hn : 0 < n) (hnN : n ≤ N)
    (hd : 0 < d) (hNd : 1 ≤ N * d ^ 2)
    (hstop : d ≤ (13 / 7) * threshold n N) :
    n * d ^ 2 ≤ 1 + (13 / 7 : ℝ) ^ 2 * Real.log (N * d ^ 2) := by
  have hN : 0 < N := lt_of_lt_of_le hn hnN
  have hlog : 0 ≤ Real.log (N * d ^ 2) := Real.log_nonneg hNd
  by_cases hsmall : n * d ^ 2 ≤ 1
  · nlinarith
  have hnd : 1 ≤ n * d ^ 2 := le_of_lt (lt_of_not_ge hsmall)
  have hratio : N / n ≤ N * d ^ 2 := by
    apply (div_le_iff₀ hn).2
    nlinarith [mul_le_mul_of_nonneg_left hnd hN.le]
  have hlogratio : Real.log (N / n) ≤ Real.log (N * d ^ 2) :=
    Real.log_le_log (div_pos hN hn) hratio
  have hNn : 1 ≤ N / n := (one_le_div hn).2 hnN
  have hbase : 0 ≤ (1 / 4 + Real.log (N / n)) / n := by
    have := Real.log_nonneg hNn
    positivity
  have hsqrt := Real.sq_sqrt hbase
  have ht := Real.sqrt_nonneg ((1 / 4 + Real.log (N / n)) / n)
  have hsquared : d ^ 2 ≤ (13 / 7 : ℝ) ^ 2 * ((1 / 4 + Real.log (N / n)) / n) := by
    dsimp [threshold] at hstop
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsquared hn.le
  have heq : n * ((13 / 7 : ℝ) ^ 2 * ((1 / 4 + Real.log (N / n)) / n)) =
      (13 / 7 : ℝ) ^ 2 * (1 / 4 + Real.log (N / n)) := by field_simp
  rw [heq] at hscaled
  nlinarith

theorem sum_cap_range (L : ℕ) : ∑ k ∈ Finset.range L, cap k = cap L - 1 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih, cap_succ]; ring

theorem finite_dyadic_indicator_sum (L : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    ∑ k ∈ Finset.range L, (if cap k ≤ a then cap k else 0) ≤ 2 * a := by
  induction L with
  | zero => simp; positivity
  | succ L ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · have hb : (∑ k ∈ Finset.range L, if cap k ≤ a then cap k else 0) ≤ cap L - 1 := by
        rw [← sum_cap_range]
        apply Finset.sum_le_sum
        intro k hk
        split_ifs <;> linarith [cap_pos k]
      linarith
    · simpa using ih

theorem finite_dyadic_scaled_indicator_sum (L : ℕ) (d A : ℝ) (hd : 0 < d)
    (hA : 0 ≤ A) :
    ∑ k ∈ Finset.range L, (if cap k * d ^ 2 ≤ A then cap k else 0) ≤
      2 * A / d ^ 2 := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  simpa only [le_div_iff₀ hd2, mul_div_assoc] using
    finite_dyadic_indicator_sum L (A / d ^ 2) (div_nonneg hA hd2.le)

private theorem exp_step_v1 (t : ℝ) :
    t * Real.exp (-t) ≤ 2 * (Real.exp (-(t / 2)) - Real.exp (-t)) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t / 2))
    (Real.exp_pos (-t)).le
  have heq : Real.exp (t / 2) * Real.exp (-t) = Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  nlinarith only [h]

theorem finite_dyadic_sum_v1 (b : ℝ) (hb : 0 < b) (L : ℕ) :
    ∑ k ∈ Finset.range L, cap k * Real.exp (-(b * cap k)) ≤ 2 / b := by
  have hpartial : ∀ m : ℕ,
      b * (∑ k ∈ Finset.range m, cap k * Real.exp (-(b * cap k))) ≤
        2 * (Real.exp (-(b / 2)) - Real.exp (-(b * cap m / 2))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hpow : b * cap (m + 1) / 2 = b * cap m := by rw [cap_succ]; ring
      rw [hpow]
      have hs := exp_step_v1 (b * cap m)
      nlinarith only [ih, hs]
  apply (le_div_iff₀ hb).2
  have hs := hpartial L
  have hstart : Real.exp (-(b / 2)) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -(b / 2) ≤ 0 by linarith)
  have hend := (Real.exp_pos (-(b * cap L / 2))).le
  nlinarith only [hs, hstart, hend]

theorem finite_work_survival_bound (L : ℕ) (d : ℝ) (hd : 0 < d)
    (hdmax : d ≤ 1 / 2) (hscale : 1 ≤ cap L * d ^ 2) :
    1 + (∑ k ∈ Finset.range L, cap k *
      ((if d ≤ (13 / 7) * threshold (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2 * (6 / 13 : ℝ) ^ 2 * d ^ 2 * cap k)))) ≤
      7 * (d⁻¹) ^ 2 * (1 + Real.log (cap L * d ^ 2)) := by
  classical
  let A := 1 + (13 / 7 : ℝ) ^ 2 * Real.log (cap L * d ^ 2)
  have hlog : 0 ≤ Real.log (cap L * d ^ 2) := Real.log_nonneg hscale
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hI : (∑ k ∈ Finset.range L, cap k *
      (if d ≤ (13 / 7) * threshold (cap k) (cap L) then 1 else 0)) ≤
        2 * A / d ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range L, if cap k * d ^ 2 ≤ A then cap k else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkL : cap k ≤ cap L := by
          unfold cap
          gcongr
          · norm_num
          · exact (Finset.mem_range.mp hk).le
        split_ifs with h h' h'
        · simp
        · have := survival_indicator_scale_step (cap k) (cap L) d (cap_pos k) hkL hd hscale h
          exact (h' this).elim
        · simpa using (cap_pos k).le
        · simp
      _ ≤ _ := finite_dyadic_scaled_indicator_sum L d A hd hA
  have hb : 0 < 2 * (6 / 13 : ℝ) ^ 2 * d ^ 2 := by positivity
  have hE := finite_dyadic_sum_v1 (2 * (6 / 13 : ℝ) ^ 2 * d ^ 2) hb L
  have hsum : 1 + (∑ k ∈ Finset.range L, cap k *
      ((if d ≤ (13 / 7) * threshold (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2 * (6 / 13 : ℝ) ^ 2 * d ^ 2 * cap k)))) ≤
      1 + 2 * A / d ^ 2 + 2 / (2 * (6 / 13 : ℝ) ^ 2 * d ^ 2) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    linarith
  apply le_trans hsum
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hdone : (1 : ℝ) ≤ (1 / 4) / d ^ 2 := by
    apply (le_div_iff₀ hd2).2
    nlinarith
  have hcoeff : (125 / 18 : ℝ) + (338 / 49 : ℝ) * Real.log (cap L * d ^ 2) ≤
      7 * (1 + Real.log (cap L * d ^ 2)) := by nlinarith
  calc
    _ ≤ (1 / 4) / d ^ 2 + 2 * A / d ^ 2 + 2 / (2 * (6 / 13 : ℝ) ^ 2 * d ^ 2) := by linarith
    _ = ((125 / 18 : ℝ) + (338 / 49 : ℝ) * Real.log (cap L * d ^ 2)) / d ^ 2 := by
      dsimp [A]
      field_simp
      <;> ring
    _ ≤ (7 * (1 + Real.log (cap L * d ^ 2))) / d ^ 2 :=
      div_le_div_of_nonneg_right hcoeff hd2.le
    _ = _ := by field_simp

end ThresholdHC.Uniform713
