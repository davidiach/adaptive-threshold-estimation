import ThresholdHC.PowerQuantileRows.Specification
import ThresholdHC.ShiftedPower.TailRates

/-! The inline row formulas of `powerRow` agree with the rate definitions of the
separately checked row theorems: `ShiftedPower.linearRate` at `α = 1`,
`ShiftedPower.intermediateRate` for `1 < α < 2`, and `RareAboveTwo.aboveTwoRate`
for `α > 2` at `x = (a √B)⁻¹`. These identities only fix notation; no proof in
this group uses the row theorems themselves. -/
noncomputable section
namespace ThresholdHC.PowerQuantileRows

theorem powerRow_eq_linearRate (x ρ : ℝ) :
    powerRow 1 x ρ = ThresholdHC.ShiftedPower.linearRate ρ x := by
  unfold powerRow ThresholdHC.ShiftedPower.linearRate
  rw [ite_eq_right (lt_irrefl (1 : ℝ)), ite_eq_left rfl]

theorem powerRow_eq_intermediateRate {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (x ρ : ℝ) :
    powerRow α x ρ = ThresholdHC.ShiftedPower.intermediateRate α ρ x := by
  unfold powerRow ThresholdHC.ShiftedPower.intermediateRate
  rw [ite_eq_right (not_lt.2 hα1.le), ite_eq_right (ne_of_gt hα1), ite_eq_left hα2]

theorem powerRow_eq_aboveTwoRate {α : ℝ} (hα2 : 2 < α) (a ρ B : ℝ) :
    powerRow α (1 / (a * Real.sqrt B)) ρ = ThresholdHC.RareAboveTwo.aboveTwoRate a ρ B := by
  have hα1 : 1 < α := by linarith
  unfold powerRow ThresholdHC.RareAboveTwo.aboveTwoRate
  rw [ite_eq_right (not_lt.2 hα1.le), ite_eq_right (ne_of_gt hα1),
    ite_eq_right (not_lt.2 hα2.le), ite_eq_right hα2.ne', mul_one_div]

end ThresholdHC.PowerQuantileRows
