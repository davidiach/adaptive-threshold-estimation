import ThresholdHC.FiniteQuantile.SmallBudget

/-! Exact types and transitive axioms for the verified direct-proof components. -/

open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open ThresholdHC.FiniteQuantile

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hB : 0 < B) (hsmall : B * ρ ≤ 1) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ 30001 * closedQuantileValue μ ρ B :=
  small_budget_explicit_bounds μ hρ hρ4 hB hsmall

#print axioms ThresholdHC.FiniteQuantile.DirectFiniteLawStatement
#print axioms ThresholdHC.FiniteQuantile.ExplicitBounds
#print axioms ThresholdHC.FiniteQuantile.small_budget_lower
#print axioms ThresholdHC.FiniteQuantile.small_budget_explicit_bounds
