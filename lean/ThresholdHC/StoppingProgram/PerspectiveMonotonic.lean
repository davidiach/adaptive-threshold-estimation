import ThresholdHC.StoppingProgram.Perspective

/-! Order properties of the closed perspective, with its null-state convention. -/

noncomputable section
open scoped ENNReal
namespace ThresholdHC.StoppingProgram

theorem perspective_antitone_reference (x : ℝ) {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    perspective x z ≤ perspective x y := by
  by_cases hy0 : y = 0
  · subst y
    by_cases hx : x = 0
    · subst x
      simp [perspective]
    · rw [perspective_nonzero_zero hx]
      exact le_top
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [perspective_pos (hy'.trans_le hyz),perspective_pos hy']
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (sq_nonneg x) hy' hyz)

end ThresholdHC.StoppingProgram
