import ThresholdHC.EntropyTailQuantile.Model

/-!
Unproved full targets: definitions of propositions, not inhabitants.
The lower-bound statistical target belongs to the separately assigned work.
No classifier bound, compactness assertion, or hidden-label oracle is an
assumption of the targets below.
-/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

def QuantileSplitStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ → ρ ≤ 1/4 →
    0 < quantileThreshold μ ρ ∧ quantileThreshold μ ρ ≤ 1/2 ∧
    quantileTail μ ρ ≤ μ ∧ (quantileTail μ ρ) Set.univ = ENNReal.ofReal ρ ∧
    quantileTail μ ρ + quantileCore μ ρ = μ ∧
    (∀ᵐ d : Gap ∂quantileTail μ ρ, (d:ℝ) ≤ quantileThreshold μ ρ) ∧
    (∀ᵐ d : Gap ∂quantileCore μ ρ, quantileThreshold μ ρ ≤ (d:ℝ)) ∧
    measureCostEntropy (quantileCore μ ρ) < ⊤

def QuantileComparisonStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    selectionValue μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (1+2*sqrt 2) * selectionValue μ ρ B

/-- Exact constant of the general-law paper, in the unchanged observable model. -/
def EntropyTailUpperStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 33000 * selectionValue μ ρ B

def ClosedQuantileUpperStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 33000 * closedQuantileValue μ ρ B

end ThresholdHC.EntropyTailQuantile
