import ThresholdHC.Genie.OptimizedBrackets

/-! Target statements for the square-root cap comparison of the optimized
stopping programs. They use only the existing ordinary and genie program
definitions. -/
noncomputable section
namespace ThresholdHC.SquareRootCap
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.RareAboveTwo

/-- The ordinary program at cap N is within the factor k of the genie
program whenever B is at most N (k - 1/k)^2. -/
def SquareRootCapStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B k : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → 1 < k → ∀ N : ℕ, B ≤ N * (k - 1/k)^2 →
    programValue μ ρ B N ≤ ENNReal.ofReal k * genieValue μ ρ B N

/-- A cap of 4B/9 passes the factor-two test and gives the factor-sixteen
minimax certificate. -/
def FourNinthsCapStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ, 4 * B / 9 ≤ N →
    programValue μ ρ B N ≤ 2 * genieValue μ ρ B N ∧
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 16 * rareMinimaxRisk μ ρ B

end ThresholdHC.SquareRootCap
