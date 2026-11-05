import Mathlib

noncomputable section
namespace ThresholdHC.ContinuousObserved

def normalizedGap (d : ℝ) : ℝ := 2 * d / Real.sqrt (1 - 4 * d ^ 2)

def inverseNormalizedGap (z : ℝ) : ℝ := z / (2 * Real.sqrt (1 + z ^ 2))

def inverseSlope (z : ℝ) : ℝ := 1 / (2 * (1 + z ^ 2) * Real.sqrt (1 + z ^ 2))

theorem inverseSlope_pos (z : ℝ) : 0 < inverseSlope z := by
  unfold inverseSlope
  have hp : 0 < 1 + z ^ 2 := by positivity
  exact div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) hp) (Real.sqrt_pos.mpr hp))

theorem inverseSlope_le (z : ℝ) : inverseSlope z ≤ 1 / 2 := by
  have hp : 1 ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have hs : 1 ≤ Real.sqrt (1 + z ^ 2) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp
  unfold inverseSlope
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith [mul_le_mul hp hs (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]

theorem hasDerivAt_inverseNormalizedGap (z : ℝ) :
    HasDerivAt inverseNormalizedGap (inverseSlope z) z := by
  have hp : 0 < 1 + z ^ 2 := by positivity
  have hs : Real.sqrt (1 + z ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hd := (hasDerivAt_id z).div
    (((((hasDerivAt_id z).pow 2).const_add 1).sqrt hp.ne').const_mul 2)
    (mul_ne_zero (by norm_num) hs)
  convert hd using 1
  · rfl
  · dsimp [inverseSlope]
    field_simp
    nlinarith [Real.sq_sqrt hp.le]

theorem inverse_normalized_gap {d : ℝ} (hd : |d| < 1 / 2) :
    inverseNormalizedGap (normalizedGap d) = d := by
  have hp : 0 < 1 - 4 * d ^ 2 := by
    have hb := abs_lt.mp hd
    nlinarith [hb.1,hb.2]
  have hs : 0 < Real.sqrt (1 - 4 * d ^ 2) := Real.sqrt_pos.mpr hp
  have hs' : Real.sqrt (1 - d ^ 2 * 4) ≠ 0 := by
    simpa only [mul_comm (d ^ 2) (4 : ℝ)] using hs.ne'
  have he : 1 + (normalizedGap d) ^ 2 = (1 / Real.sqrt (1 - 4 * d ^ 2)) ^ 2 := by
    unfold normalizedGap
    field_simp [hs.ne',hs']
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 - d ^ 2 * 4 by nlinarith [hp])]
  unfold inverseNormalizedGap
  rw [he,Real.sqrt_sq (div_nonneg (by norm_num) hs.le)]
  unfold normalizedGap
  field_simp [hs.ne',hs']

end ThresholdHC.ContinuousObserved
