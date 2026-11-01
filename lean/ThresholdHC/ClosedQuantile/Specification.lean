import ThresholdHC.EntropyTailQuantile.Model

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ClosedQuantile
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile

/-- The closed quantile rate in the original observable experiment, for every
probability law, including atoms and infinite support. Constants are universal;
the paper's explicit lower coefficient and its direct finite-law argument are
not asserted by this corollary. -/
def ClosedQuantileLawStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal c * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal C * closedQuantileValue μ ρ B

end ThresholdHC.ClosedQuantile
