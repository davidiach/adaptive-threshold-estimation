import ThresholdHC.EntropyTail.Model
import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

/-! Stability statements for the original capped selection functional (certified-selection
Theorems 7 and 8). Mathlib's total variation norm of two probabilities has range [0,2]. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.SelectionStability
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def TVStatement : Prop :=
  ∀ (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    |(selection μ ρ B).toReal - (selection ν ρ B).toReal| ≤ tvDist μ ν / 2

def RoundingStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (T : Gap → Gap), Measurable T →
    ∀ {r ρ B : ℝ}, 1 ≤ r → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) →
    (∀ j, T ⁻¹' band j = band j) →
    selection (μ.map T) ρ B ≤ selection μ ρ B ∧
    selection μ ρ B ≤ ENNReal.ofReal r * selection (μ.map T) ρ B

end ThresholdHC.SelectionStability
