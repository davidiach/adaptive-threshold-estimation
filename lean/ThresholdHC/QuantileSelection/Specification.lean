import ThresholdHC.EntropyTailQuantile.Model

/-! The two entropy estimates and the capped comparison of Theorem 4
in the certified-selection note. The gap law may have a quantile atom. -/
noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.QuantileSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

def InteractionStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
    costEntropy (fun i => a i + b i) ≤ costEntropy a + costEntropy b +
      2 * log 2 * sqrt (costTotal a * costTotal b) ∧
    costEntropy a + costEntropy b + 2 * log 2 * sqrt (costTotal a * costTotal b) ≤
      costEntropy a + costEntropy b + sqrt (2 * costEntropy a * costEntropy b)

def SeparatedCostStatement : Prop :=
  ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ] {t : ℝ}, 0 < t →
    (∀ᵐ d : Gap ∂ξ, t ≤ (d : ℝ)) →
    measureCostEntropy ξ ≤ ENNReal.ofReal ((2 / t) * ∫ d : Gap, (d : ℝ)⁻¹ ∂ξ)

def ComparisonStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    selectionValue μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * selectionValue μ ρ B ∧
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) (budgetScale B)) ≤ selectionValue μ ρ B ∧
    (quantileThreshold μ ρ ≤ budgetScale B →
      selectionValue μ ρ B = ENNReal.ofReal ρ ∧ closedQuantileValue μ ρ B = ENNReal.ofReal ρ)

end ThresholdHC.QuantileSelection
