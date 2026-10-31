import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Elementary surcharge estimates. The deliberately looser constants avoid
transcendental numerical estimates and leave room in the final upper constant. -/

noncomputable section
open Real

namespace ThresholdHC.EntropyTailUpper

def logPlus (x : ℝ) : ℝ := max 0 (log x)

theorem logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := le_max_left _ _

theorem logPlus_eq_log_max {x : ℝ} (hx : 0 ≤ x) : logPlus x = log (max 1 x) := by
  by_cases h : x ≤ 1
  · rw [logPlus, max_eq_left (log_nonpos hx h), max_eq_left h, log_one]
  · rw [logPlus, max_eq_right (log_nonneg (le_of_not_ge h)), max_eq_right (le_of_not_ge h)]

theorem logPlus_le_self {x : ℝ} (hx : 0 ≤ x) : logPlus x ≤ x := by
  apply max_le hx
  exact log_le_self hx

theorem logPlus_le_half_sq {x : ℝ} (hx : 0 ≤ x) : logPlus x ≤ x^2/2 := by
  by_cases h : x ≤ 1
  · rw [logPlus, max_eq_left (log_nonpos hx h)]
    positivity
  · have hx0 : 0 < x := by linarith
    have hl := log_le_sub_one_of_pos (sq_pos_of_pos hx0)
    rw [log_pow] at hl
    norm_num at hl
    apply max_le (by positivity)
    linarith

theorem logPlus_three_term {z x y : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    logPlus (z+x+y) ≤ log 3+logPlus x+logPlus y := by
  have hX := le_max_left (1:ℝ) x
  have hY := le_max_left (1:ℝ) y
  have hxy : 1 ≤ max 1 x * max 1 y := by nlinarith
  have hxx : x ≤ max 1 x * max 1 y := (le_max_right _ _).trans (by nlinarith)
  have hyy : y ≤ max 1 x * max 1 y := (le_max_right _ _).trans (by nlinarith)
  have hb : z+x+y ≤ 3*(max 1 x*max 1 y) := by linarith
  have hpos : 0 < 3*(max 1 x*max 1 y) := by positivity
  have hlog : log (z+x+y) ≤ log (3*(max 1 x*max 1 y)) := by
    by_cases hz : z+x+y = 0
    · rw [hz, log_zero]
      exact log_nonneg (by nlinarith)
    · exact log_le_log (lt_of_le_of_ne (by positivity) (Ne.symm hz)) hb
  rw [log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
    log_mul (by positivity : max 1 x ≠ 0) (by positivity : max 1 y ≠ 0),
    ← logPlus_eq_log_max hx, ← logPlus_eq_log_max hy] at hlog
  apply max_le
  · have := log_nonneg (by norm_num : (1:ℝ) ≤ 3)
    linarith [logPlus_nonneg x, logPlus_nonneg y]
  · linarith

theorem log_surcharge_bound {z A H ρ d : ℝ} (hz : 0 ≤ z) (hzρ : z ≤ ρ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hρ : 0 < ρ) (hd : 0 < d) :
    d⁻¹^2 * logPlus ((z+A*d^2+H*d)/ρ) ≤
      log 3*d⁻¹^2 + A/ρ + H^2/(2*ρ^2) := by
  have he : (z+A*d^2+H*d)/ρ = z/ρ+(A*d^2)/ρ+(H*d)/ρ := by ring
  rw [he]
  have hl := logPlus_three_term (div_nonneg hz hρ.le) ((div_le_one hρ).mpr hzρ)
    (div_nonneg (mul_nonneg hA (sq_nonneg d)) hρ.le) (div_nonneg (mul_nonneg hH hd.le) hρ.le)
  have ha := logPlus_le_self (div_nonneg (mul_nonneg hA (sq_nonneg d)) hρ.le)
  have hh := logPlus_le_half_sq (div_nonneg (mul_nonneg hH hd.le) hρ.le)
  have hb := mul_le_mul_of_nonneg_left (hl.trans (add_le_add (add_le_add le_rfl ha) hh)) (sq_nonneg d⁻¹)
  have hr : d⁻¹^2*(log 3+A*d^2/ρ+(H*d/ρ)^2/2) = log 3*d⁻¹^2+A/ρ+H^2/(2*ρ^2) := by
    field_simp [hρ.ne', hd.ne']
  exact hb.trans_eq hr

end ThresholdHC.EntropyTailUpper
