import SharpCap

open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie
  ThresholdHC.RareAboveTwo ThresholdHC.CapReview

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B k : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → 1 < k → ∀ N : ℕ, B ≤ N*(k-1/k)^2 →
    programValue μ ρ B N ≤ ENNReal.ofReal k * genieValue μ ρ B N :=
  @square_root_cap_factor

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ, 4*B/9 ≤ N →
    programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B :=
  @four_ninths_cap

#print axioms square_root_cap_factor
#print axioms four_ninths_cap
