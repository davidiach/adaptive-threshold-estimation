import ThresholdHC.EntropyTail.QuantileSplit

/-! The actual quantile core is a feasible selection submeasure. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

theorem sub_quantileCore (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : μ - quantileCore μ ρ = quantileTail μ ρ := by
  have : IsFiniteMeasure (quantileCore μ ρ) := by
    unfold quantileCore
    infer_instance
  calc
    μ - quantileCore μ ρ = (quantileTail μ ρ + quantileCore μ ρ) - quantileCore μ ρ := by
      rw [quantileTail_add_core μ hρ hρ1]
    _ = quantileTail μ ρ := Measure.add_sub_cancel

theorem selectionValue_le_closedQuantileValue (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    selectionValue μ ρ B ≤ closedQuantileValue μ ρ B := by
  unfold selectionValue closedQuantileValue
  apply min_le_min_left
  have hc : quantileCore μ ρ ≤ μ := Measure.sub_le
  apply le_trans (iInf_le_of_le (quantileCore μ ρ) (iInf_le _ hc))
  simp only [selectionCost, sub_quantileCore μ hρ hρ1, add_comm, le_refl]

end ThresholdHC.EntropyTail
