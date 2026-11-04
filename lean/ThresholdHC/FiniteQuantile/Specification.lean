import ThresholdHC.EntropyTailQuantile.Model

/-! The explicit finite-law target of Appendix O, with the original observable
experiment and fractional boundary atom. The universal entropy-tail lower
theorem is not an input to the direct proof. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

def ExplicitBounds (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) : Prop :=
  ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ 30001 * closedQuantileValue μ ρ B

def DirectFiniteLawStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1 / 4 → 0 < B → ExplicitBounds μ ρ B

end ThresholdHC.FiniteQuantile
