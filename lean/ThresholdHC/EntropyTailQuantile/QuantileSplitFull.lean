import ThresholdHC.EntropyTailQuantile.Specification
import ThresholdHC.EntropyTailQuantile.QuantileSplit
import ThresholdHC.EntropyTailQuantile.MeasureEntropy

namespace ThresholdHC.EntropyTailQuantile

/-- The frozen arbitrary-law quantile split, with a fractional boundary atom. -/
theorem quantile_split : QuantileSplitStatement := by
  intro μ _ ρ hρ hρ4
  have hρ1 : ρ ≤ 1 := by linarith
  have ht := quantileThreshold_properties μ hρ hρ1
  exact ⟨ht.1, ht.2.1, quantileTail_le μ hρ hρ1, quantileTail_mass μ hρ hρ1,
    quantileTail_add_core μ hρ hρ1, quantileTail_support μ ρ, quantileCore_support μ ρ,
    measureCostEntropy_lt_top_of_support _ ht.1 (quantileCore_support μ ρ)⟩

end ThresholdHC.EntropyTailQuantile
