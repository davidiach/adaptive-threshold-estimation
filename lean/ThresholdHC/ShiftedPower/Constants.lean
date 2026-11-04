import ThresholdHC.ShiftedPower.Linear
import ThresholdHC.ShiftedPower.Intermediate

noncomputable section
open Real
namespace ThresholdHC.ShiftedPower

theorem workConstant_formula {α : ℝ} (hα : 0 < α) (hu : α < 2) :
    workConstant α = 68*(α+2)/(2-α)^2 := by
  have hp : α+2 ≠ 0 := by linarith
  have hq : 2-α ≠ 0 := by linarith
  have hfirst : 1-workPower α/2 = (2-α)/4 := by unfold workPower; ring
  have hsecond : 1-α/workPower α = (2-α)/(α+2) := by
    unfold workPower
    field_simp [hp]
    ring
  unfold workConstant
  rw [hfirst,hsecond]
  field_simp [hq]
  ring

theorem linearConstant_le : linearConstant ≤ 287 := by
  have hw : workConstant 1 = 204 := by norm_num [workConstant,workPower]
  have hs : sqrt (204:ℝ) ≤ 143/10 := Real.sqrt_le_iff.mpr (by norm_num)
  unfold linearConstant
  rw [hw]
  linarith only [hs]

end ThresholdHC.ShiftedPower
