import ThresholdHC.QuantileSharpLaw.Full

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

def FiniteSharpnessStatement : Prop :=
  ∀ k : ℝ, k < scalarRoot →
    ∃ (μ : Measure Gap) (_ : IsProbabilityMeasure μ),
      μ.support.Finite ∧ ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < B ∧
        ENNReal.ofReal k*ThresholdHC.EntropyTail.selection μ ρ B < closedQuantileValue μ ρ B

def UniversalFactor (k : ℝ) : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal k*ThresholdHC.EntropyTail.selection μ ρ B

def FiniteUniversalFactor (k : ℝ) : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal k*ThresholdHC.EntropyTail.selection μ ρ B

end ThresholdHC.QuantileOptimality
