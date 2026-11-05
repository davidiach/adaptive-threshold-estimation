
import ThresholdHC.AnytimeLower.TestingSchedule

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower

def budgetInflation (δ : ℝ) (n : ℕ) : ℝ := log (1/δ)+log (log (n:ℝ))

theorem loglog_polynomial_bound {n x D : ℝ} (hn : 1 < n) (hx : 0 < x)
    (hD : 0 < D) (hb : log n ≤ D*x^2) :
    log (log n) ≤ log D+2*log x := by
  have h := log_le_log (log_pos hn) hb
  rw [log_mul hD.ne' (pow_ne_zero 2 hx.ne'),log_pow] at h
  simpa using h

theorem geometric_loglog_bound {n C x : ℝ} (hn : 1 < n) (hC : 0 < C)
    (hx : 1 ≤ x) (j : ℕ) (hj : (j:ℝ) ≤ x^2)
    (hb : n ≤ C*(16:ℝ)^j*x) :
    log (log n) ≤ log (|log C|+16)+2*log x := by
  apply loglog_polynomial_bound hn (by linarith) (by positivity)
  have hl := log_le_log (by linarith : 0 < n) hb
  rw [log_mul (mul_ne_zero hC.ne' (pow_ne_zero j (by norm_num))) (by linarith : x ≠ 0),
    log_mul hC.ne' (pow_ne_zero j (by norm_num)),log_pow] at hl
  have h16 : log (16:ℝ) ≤ 15 := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)]
  have hxlog := log_le_sub_one_of_pos (by linarith : 0 < x)
  have hj0 := Nat.cast_nonneg (α:=ℝ) j
  have hp := mul_nonneg (abs_nonneg (log C)) (show 0 ≤ x^2-1 by nlinarith)
  have hpow := mul_nonneg (show 0 ≤ x-1 by linarith) (show 0 ≤ x by linarith)
  nlinarith [le_abs_self (log C),mul_le_mul_of_nonneg_left h16 hj0]

theorem geometric_inflation_eventually (δ C : ℝ) (hC : 0 < C)
    (j N : ℕ → ℕ)
    (hj : ∀ᶠ k in atTop, (j k:ℝ) ≤ ((k:ℝ)+2)^2)
    (hN : Tendsto N atTop atTop)
    (hb : ∀ k, (N k:ℝ) ≤ C*(16:ℝ)^(j k)*((k:ℝ)+2)) :
    ∀ᶠ k in atTop, budgetInflation δ (N k) ≤ 3*log ((k:ℝ)+2) := by
  have hl : Tendsto (fun k : ℕ => log ((k:ℝ)+2)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop)
  filter_upwards [hj,hN.eventually (eventually_ge_atTop 2),
    hl.eventually (eventually_ge_atTop (log (1/δ)+log (|log C|+16)))] with k hjk hNk hlog
  have hn : (1:ℝ) < N k := by exact_mod_cast (show 1 < N k by omega)
  have hx : (1:ℝ) ≤ (k:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) k; linarith
  have he := geometric_loglog_bound hn hC hx (j k) hjk (hb k)
  unfold budgetInflation
  linarith

end ThresholdHC.AnytimeLower
