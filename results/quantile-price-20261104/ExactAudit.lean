import ThresholdHC.QuantilePrice.Full
import ThresholdHC.QuantileSelection.Interaction
import ThresholdHC.QuantileSelection.SeparatedCost
import ThresholdHC.QuantileSelection.Full
example : ThresholdHC.QuantileSelection.InteractionStatement := ThresholdHC.QuantileSelection.entropy_interaction
example : ThresholdHC.QuantileSelection.SeparatedCostStatement := ThresholdHC.QuantileSelection.separated_cost
example : ThresholdHC.QuantileSelection.ComparisonStatement := ThresholdHC.QuantileSelection.quantile_selection_comparison
example (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ] {ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hb : 0 < B) : ThresholdHC.EntropyTail.selection μ ρ B ≤ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * ThresholdHC.EntropyTail.selection μ ρ B := ThresholdHC.QuantileSelection.locked_selection_comparison μ hρ hr hb
#print axioms ThresholdHC.QuantileSelection.ComparisonStatement
#print axioms ThresholdHC.QuantileSelection.InteractionStatement
#print axioms ThresholdHC.QuantileSelection.SeparatedCostStatement
#print axioms ThresholdHC.QuantileSelection.binEntropy_le_geometric
#print axioms ThresholdHC.QuantileSelection.binary_interaction
#print axioms ThresholdHC.QuantileSelection.comparison_pointwise
#print axioms ThresholdHC.QuantileSelection.comparison_pointwise_of_price
#print axioms ThresholdHC.QuantileSelection.core_interaction
#print axioms ThresholdHC.QuantileSelection.core_price
#print axioms ThresholdHC.QuantileSelection.entropy_interaction
#print axioms ThresholdHC.QuantileSelection.entropy_slope_nonneg
#print axioms ThresholdHC.QuantileSelection.entropy_superadditive
#print axioms ThresholdHC.QuantileSelection.locked_selection_comparison
#print axioms ThresholdHC.QuantileSelection.quantile_selection_comparison
#print axioms ThresholdHC.QuantileSelection.scaleWeight
#print axioms ThresholdHC.QuantileSelection.scaleWeight_band
#print axioms ThresholdHC.QuantileSelection.scaleWeight_coefficient
#print axioms ThresholdHC.QuantileSelection.scaleWeight_mass
#print axioms ThresholdHC.QuantileSelection.scaleWeight_pos
#print axioms ThresholdHC.QuantileSelection.selection_triangle
#print axioms ThresholdHC.QuantileSelection.separated_cost
#print axioms ThresholdHC.QuantileSelection.separated_cost_of_weights

open MeasureTheory Real ThresholdHC.Tier6
open scoped ENNReal
example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hr : 0 < ρ)
    (hr' : ρ ≤ 1/4) (hb : 0 < B) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧
    ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ≤
      ENNReal.ofReal (31/20)*ThresholdHC.EntropyTail.selection μ ρ B :=
  ThresholdHC.QuantilePrice.quantile_le_31_20_selection μ hr hr' hb
example (Z : Measure Gap) [IsFiniteMeasure Z] {t : ℝ} (ht : 0 < t)
    (hs : ∀ᵐ d : Gap ∂Z, t ≤ (d:ℝ)) :
    ThresholdHC.EntropyTailQuantile.measureCostEntropy Z ≤
      ENNReal.ofReal (((16/9)/t)*∫ d : Gap, (d:ℝ)⁻¹ ∂Z) := ThresholdHC.QuantilePrice.separated_cost Z ht hs
#print axioms ThresholdHC.QuantilePrice.price_quartic
#print axioms ThresholdHC.QuantilePrice.quantile_le_31_20_selection
#print axioms ThresholdHC.QuantilePrice.scalar_price
#print axioms ThresholdHC.QuantilePrice.separated_cost
#print axioms ThresholdHC.QuantilePrice.weight
#print axioms ThresholdHC.QuantilePrice.weight_band
#print axioms ThresholdHC.QuantilePrice.weight_coefficient
#print axioms ThresholdHC.QuantilePrice.weight_mass
#print axioms ThresholdHC.QuantilePrice.weight_pos
