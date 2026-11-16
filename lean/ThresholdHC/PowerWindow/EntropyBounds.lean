import ThresholdHC.PowerWindow.Specification
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
namespace ThresholdHC.PowerWindow

/-- The lower uniform entropy constant from a bound on every cell mass. -/
theorem entropy_window_lower {M s N E : ℝ} (hM : 0 < M) (hs : 0 ≤ s)
    (hN : 1 ≤ N) (hNM : N ≤ 1 + M) (hNs : 2 ≤ N → N * s ≤ 1)
    (hE : 0 ≤ E) (hatom : -Real.log (1/M + s * Real.log 2) ≤ E) :
    (1/2 : ℝ) * (1 + Real.log N) ≤ 1 + E := by
  have hN0 : 0 < N := by linarith
  by_cases hN2 : N ≤ 2
  · have hlog := Real.log_le_log hN0 hN2
    linarith [Real.log_two_lt_d9]
  · have h2N : 2 ≤ N := (not_le.1 hN2).le
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hC : 0 < 2 + Real.log 2 := by linarith
    have hR : 0 < 1/M + s * Real.log 2 :=
      add_pos_of_pos_of_nonneg (one_div_pos.2 hM) (mul_nonneg hs hl2)
    have hratio : N / M ≤ 2 := (div_le_iff₀ hM).2 (by linarith)
    have hprod : N * (1/M + s * Real.log 2) ≤ 2 + Real.log 2 := by
      have hp := mul_le_mul_of_nonneg_right (hNs h2N) hl2
      calc
        _ = N/M + N*s*Real.log 2 := by ring
        _ ≤ 2 + Real.log 2 := add_le_add hratio (by simpa using hp)
    have hb : 1/M + s * Real.log 2 ≤ (2 + Real.log 2) / N := by
      apply (le_div_iff₀ hN0).2
      simpa only [mul_comm N] using hprod
    have hlog := Real.log_le_log hR hb
    rw [Real.log_div hC.ne' hN0.ne'] at hlog
    have hC1 : Real.log (2 + Real.log 2) ≤ 1 :=
      (Real.log_le_iff_le_exp hC).2 (by linarith [Real.log_two_lt_d9, Real.exp_one_gt_d9])
    linarith

/-- Cardinality and a geometric first-moment bound together give the uniform
upper constant. The slack avoids numerical optimization of geometric entropy. -/
theorem entropy_window_upper {M s E : ℝ} (hM : 0 < M) (hs : 0 ≤ s)
    (hcount : E ≤ Real.log (M + 2))
    (hmoment : 0 < s → E ≤ 1 + Real.log (2 + 2/s)) :
    1 + E ≤ (383/100 : ℝ) *
      (1 + Real.log (if s = 0 then 1 + M else min (1 + M) (max 1 (1/s)))) := by
  have hM1 : 0 < 1 + M := by linarith
  have hlogM : 0 ≤ Real.log (1 + M) := Real.log_nonneg (by linarith)
  have hcount' : E ≤ Real.log 2 + Real.log (1 + M) := by
    have h := Real.log_le_log (by linarith : 0 < M + 2)
      (show M + 2 ≤ 2 * (1 + M) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hM1.ne'] at h
    exact hcount.trans h
  have hMbound : 1 + E ≤ (383/100 : ℝ) * (1 + Real.log (1 + M)) := by
    linarith [Real.log_two_lt_d9]
  by_cases hs0 : s = 0
  · simpa only [ite_eq_left hs0] using hMbound
  · rw [ite_eq_right hs0]
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hmin : 1 + M ≤ max 1 (1/s)
    · simpa only [min_eq_left hmin] using hMbound
    · rw [min_eq_right (not_le.1 hmin).le]
      have hG : 0 < max 1 (1/s) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hGlog : 0 ≤ Real.log (max 1 (1/s)) := Real.log_nonneg (le_max_left _ _)
      have hb : 2 + 2/s ≤ 4 * max 1 (1/s) := by
        have h1 := le_max_left (1 : ℝ) (1/s)
        have h2 := le_max_right (1 : ℝ) (1/s)
        calc
          _ = 2 + 2 * (1/s) := by ring
          _ ≤ 4 * max 1 (1/s) := by linarith
      have hl := Real.log_le_log (by positivity : 0 < 2 + 2/s) hb
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hG.ne'] at hl
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [hlog4] at hl
      linarith [hmoment hspos, Real.log_two_lt_d9]

end ThresholdHC.PowerWindow
