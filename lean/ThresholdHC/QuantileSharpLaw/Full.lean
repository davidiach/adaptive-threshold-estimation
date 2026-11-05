import ThresholdHC.QuantileSharpLaw.Pointwise
import ThresholdHC.EntropyTail.Bridge

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem quantile_le_scalarRoot_selection (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B) :
    selectionValue μ ρ B ≤ closedQuantileValue μ ρ B ∧
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal scalarRoot*selectionValue μ ρ B := by
  have hk1 : 1 ≤ scalarRoot :=
    (one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans scalarRoot_spec.1.1
  have hf : (1 : ℝ≥0∞) ≤ ENNReal.ofReal scalarRoot := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hk1
  have hpos := ne_of_gt (lt_of_lt_of_le zero_lt_one hf)
  refine ⟨selectionValue_le_closedQuantileValue μ hρ hρ1 B,?_⟩
  by_cases ht : quantileThreshold μ ρ ≤ budgetScale B
  · obtain ⟨hK,hQ⟩ := quantile_saturation μ hρ hρ1 ht
    rw [hK,hQ]
    simpa only [one_mul] using mul_le_mul_left hf (ENNReal.ofReal ρ)
  unfold selectionValue
  rw [mul_min]
  refine le_min ((min_le_left _ _).trans ?_) ?_
  · simpa only [one_mul] using mul_le_mul_left hf (ENNReal.ofReal ρ)
  · rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf
    intro σ
    rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    exact le_iInf (sharp_comparison_pointwise μ hρ hρ1 hB (lt_of_not_ge ht) σ)

theorem locked_sharp_quantile_comparison (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal scalarRoot*ThresholdHC.EntropyTail.selection μ ρ B := by
  rw [← ThresholdHC.EntropyTail.quantile_selectionValue_eq μ ρ B]
  exact quantile_le_scalarRoot_selection μ hρ (by linarith) hB

end ThresholdHC.QuantileSharpLaw
