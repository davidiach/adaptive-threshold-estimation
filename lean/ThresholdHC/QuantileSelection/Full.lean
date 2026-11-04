import ThresholdHC.QuantileSelection.Pointwise
import ThresholdHC.EntropyTail.Bridge

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.QuantileSelection
open ThresholdHC.EntropyTailQuantile

/-- Theorem 4 of the certified-selection note, including its tail floor and saturation claims. -/
theorem quantile_selection_comparison : ComparisonStatement := by
  intro μ _ ρ B hρ hρ4 hB
  have hρ1 : ρ ≤ 1 := by linarith
  refine ⟨selectionValue_le_closedQuantileValue μ hρ hρ1 B, ?_,
    quantileTail_le_selectionValue μ hρ hρ1 B, quantile_saturation μ hρ hρ1⟩
  have hf : (1:ℝ≥0∞) ≤ ENNReal.ofReal (8/5) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hpos := ne_of_gt (lt_of_lt_of_le zero_lt_one hf)
  by_cases ht : quantileThreshold μ ρ ≤ budgetScale B
  · obtain ⟨hK,hQ⟩ := quantile_saturation μ hρ hρ1 ht
    rw [hK, hQ]
    simpa only [one_mul] using mul_le_mul_left hf (ENNReal.ofReal ρ)
  unfold selectionValue
  rw [mul_min]
  refine le_min ((min_le_left _ _).trans ?_) ?_
  · simpa only [one_mul] using mul_le_mul_left hf (ENNReal.ofReal ρ)
  · rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf
    intro σ
    rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    exact le_iInf (comparison_pointwise μ hρ hρ1 hB (lt_of_not_ge ht) σ)

/-- The same comparison for the selection functional used in the statistical minimax theorem. -/
theorem locked_selection_comparison (μ : Measure Tier6.Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * EntropyTail.selection μ ρ B := by
  rw [← EntropyTail.quantile_selectionValue_eq μ ρ B]
  obtain ⟨hl,hu,_,_⟩ := quantile_selection_comparison μ hρ hρ4 hB
  exact ⟨hl,hu⟩

end ThresholdHC.QuantileSelection
