import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

theorem fixed_gap_unbiased : ThresholdHC.Targets.fixed_gap_unbiased := by
  intro d q hd _
  dsimp [pred]
  field_simp
  <;> ring

theorem fixed_gap_variance : ThresholdHC.Targets.fixed_gap_variance := by
  intro d q hd _
  have hne : d ≠ 0 := ne_of_gt hd
  have heq : pred d q * ((1 - 1/2 + d) / (2 * d) - q) ^ 2
      + (1 - pred d q) * ((0 - 1/2 + d) / (2 * d) - q) ^ 2
      = 1 / (16 * d ^ 2) - (q - 1/2) ^ 2 := by
    dsimp [pred]
    field_simp
    <;> ring
  rw [heq]
  nlinarith [sq_nonneg (q - 1/2)]

theorem fixed_gap_equality : ThresholdHC.Targets.fixed_gap_equality := by
  intro d hd _
  have hne : d ≠ 0 := ne_of_gt hd
  dsimp [pred]
  field_simp
  <;> ring

end ThresholdHC.Proofs
