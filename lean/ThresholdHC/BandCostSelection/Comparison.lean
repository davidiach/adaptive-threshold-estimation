import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
namespace ThresholdHC.BandCostSelection

/-- The exact branch decision used for saving differences. On rational inputs all
operations in this predicate are rational; no square-root evaluation is needed. -/
def savingPositive (x y B : ℝ) : Prop :=
  if x = 0 then 0 < y
  else if y = 0 then 0 < x
  else if (0 < x ↔ 0 < y) then 0 < x
  else if 0 < x then 0 < B*x*x-y*y else B*x*x-y*y < 0

private theorem opposite_positive {z y : ℝ} (hz : 0 < z) (hy : y < 0) :
    0 < z+y ↔ 0 < z*z-y*y := by
  have hf : 0 < z-y := by linarith
  have he : z*z-y*y = (z-y)*(z+y) := by ring
  rw [he, mul_pos_iff_of_pos_left hf]

private theorem opposite_negative {z y : ℝ} (hz : z < 0) (hy : 0 < y) :
    0 < z+y ↔ z*z-y*y < 0 := by
  have hf : z-y < 0 := by linarith
  have he : z*z-y*y = (z-y)*(z+y) := by ring
  rw [he, mul_neg_iff]
  simp [hf, hf.not_gt]

/-- The branch comparison is exact, including zero coefficients and ties. -/
theorem savingPositive_iff (x y : ℝ) {B : ℝ} (hB : 0 < B) :
    savingPositive x y B ↔ 0 < x + y / Real.sqrt B := by
  have hs := Real.sqrt_pos.mpr hB
  have hs2 := Real.sq_sqrt hB.le
  have he : 0 < x + y / Real.sqrt B ↔ 0 < x * Real.sqrt B + y := by
    rw [← mul_pos_iff_of_pos_right hs]
    field_simp
  rw [he]
  by_cases hx : x = 0
  · simp [savingPositive, hx]
  by_cases hy : y = 0
  · simp [savingPositive, hx, hy, hs]
  by_cases hxp : 0 < x
  · by_cases hyp : 0 < y
    · simp [savingPositive, hx, hy, hxp, hyp, add_pos (mul_pos hxp hs) hyp]
    · have hyn : y < 0 := lt_of_le_of_ne (le_of_not_gt hyp) hy
      rw [savingPositive, ite_eq_right hx, ite_eq_right hy, ite_eq_right (by simp [hxp, hyp]), ite_eq_left hxp]
      have heq : B*x*x-y*y = (x*Real.sqrt B)*(x*Real.sqrt B)-y*y := by nlinarith
      rw [heq]
      exact (opposite_positive (mul_pos hxp hs) hyn).symm
  · have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx
    by_cases hyp : 0 < y
    · rw [savingPositive, ite_eq_right hx, ite_eq_right hy, ite_eq_right (by simp [hxp, hyp]), ite_eq_right hxp]
      have heq : B*x*x-y*y = (x*Real.sqrt B)*(x*Real.sqrt B)-y*y := by nlinarith
      rw [heq]
      exact (opposite_negative (mul_neg_of_neg_of_pos hxn hs) hyp).symm
    · have hyn : y < 0 := lt_of_le_of_ne (le_of_not_gt hyp) hy
      have hn : ¬0 < x*Real.sqrt B+y := not_lt.mpr (le_of_lt
        (add_neg (mul_neg_of_neg_of_pos hxn hs) hyn))
      simp [savingPositive, hx, hy, hxp, hyp, hn]

end ThresholdHC.BandCostSelection

