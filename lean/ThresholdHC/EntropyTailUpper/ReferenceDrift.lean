import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Exact scalar logarithmic drift constants for the matching references. -/

noncomputable section

namespace ThresholdHC.EntropyTailUpper
open Real

theorem reference_log_base {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) :
    -(8/3:ℝ)*r^2 ≤ (1/2)*log (1-4*r^2) := by
  have hz : (3/4:ℝ) ≤ 1-4*r^2 := by nlinarith
  have hz0 : 0 < 1-4*r^2 := by linarith
  have hl := one_sub_inv_le_log_of_pos hz0
  have he : 1-(1-4*r^2)⁻¹ = -(4*r^2/(1-4*r^2)) := by
    field_simp
    ring
  rw [he] at hl
  have hb := div_le_div_of_nonneg_left (by positivity : 0 ≤ 4*r^2)
    (by norm_num : (0:ℝ) < 3/4) hz
  norm_num at hb
  linarith

theorem reference_log_ratio {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) :
    4*r ≤ log ((1+2*r)/(1-2*r)) := by
  have h := sum_range_le_log_div (by linarith : 0 ≤ 2*r) (by linarith : 2*r < 1) 1
  norm_num at h
  linarith

def negativeReferenceDrift (d r : ℝ) : ℝ :=
  (1/2-d)*log (1-2*r)+(1/2+d)*log (1+2*r)

theorem negativeReferenceDrift_eq {d r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) :
    negativeReferenceDrift d r = (1/2)*log (1-4*r^2)+d*log ((1+2*r)/(1-2*r)) := by
  have hm : 0 < 1-2*r := by linarith
  have hp : 0 < 1+2*r := by linarith
  rw [show 1-4*r^2 = (1-2*r)*(1+2*r) by ring, log_mul hm.ne' hp.ne', log_div hp.ne' hm.ne']
  unfold negativeReferenceDrift
  ring

theorem negativeReferenceDrift_lower {d r : ℝ} (hd : 0 ≤ d)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (hdr : d/2 ≤ r) (hrd : r ≤ d) :
    (4/3:ℝ)*d^2 ≤ negativeReferenceDrift d r := by
  rw [negativeReferenceDrift_eq hr0 hr1]
  have hb := reference_log_base hr0 hr1
  have hl := mul_le_mul_of_nonneg_left (reference_log_ratio hr0 hr1) hd
  have hp := mul_nonneg (sub_nonneg.mpr hdr) (sub_nonneg.mpr hrd)
  nlinarith only [hb, hl, hp]

theorem positiveReferenceDrift_lower {d r a : ℝ} (hd : 0 ≤ d)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (hdr : d/4 ≤ r) (hrd : r ≤ d/2) (ha : d/2 ≤ a) :
    d^2/3 ≤ (1/2)*log (1-4*r^2)+a*log ((1+2*r)/(1-2*r)) := by
  have hb := reference_log_base hr0 hr1
  have hr := reference_log_ratio hr0 hr1
  have hl := mul_le_mul ha hr (by positivity : (0:ℝ) ≤ 4*r) (by linarith : 0 ≤ a)
  have hp := mul_nonneg (sub_nonneg.mpr hdr) (sub_nonneg.mpr hrd)
  nlinarith only [hb, hl, hp]

theorem reference_log_overshoot {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) :
    log (1+2*r) < 1 := by
  have h := log_le_sub_one_of_pos (by linarith : 0 < 1+2*r)
  linarith

end ThresholdHC.EntropyTailUpper
