import ThresholdHC.Genie.OptimizedBrackets

/-! Target statements for the factor 3√7/2 between the infinite stopping
program and the original minimax RMS risk, and its two finite-cap
corollaries with the factor 3√7.

Source: research/2026-11-17-rms-constants/adaptive-threshold-math-review.tex,
the page headed A tighter certificate for minimax risk (page 3 of the first
review; the file has no labels): the display R ≤ P∞ ≤ (3√7/2) R, the sentence giving
R ≤ P_N ≤ 3√7 R for N ≥ ⌈4B/9⌉, and the sentence on a verified feasible upper
bound U and a genie lower bound L with U ≤ 2L, and the remark that 3√7 R < 8R,
below the published factor 8. The statements use only the
existing program, genie and minimax definitions. The proofs are in the other
modules of this group. -/
noncomputable section
namespace ThresholdHC.ProgramFactor
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.RareAboveTwo

/-- The infinite-cap stopping program is within the factor 3√7/2 of minimax
RMS risk. -/
def InfiniteProgramFactorStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ ENNReal.ofReal (3 * Real.sqrt 7 / 2) * rareMinimaxRisk μ ρ B

/-- With a cap of at least 4B/9 the finite program is within 3√7 of minimax
risk. -/
def FourNinthsFactorStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ, 4 * B / 9 ≤ N →
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ ENNReal.ofReal (3 * Real.sqrt 7) * rareMinimaxRisk μ ρ B

/-- Any upper bound U on the cap-N program and any lower bound L on the cap-N
genie value with U ≤ 2L certify the factor 3√7 for U (paper: a verified
feasible upper bound U and a genie lower bound L). Taking U the program value
and L the genie value gives the factor-two test. -/
def GenieTestFactorStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ, 0 < N → ∀ U L : ℝ≥0∞,
    programValue μ ρ B N ≤ U → L ≤ genieValue μ ρ B N → U ≤ 2 * L →
    rareMinimaxRisk μ ρ B ≤ U ∧
    U ≤ ENNReal.ofReal (3 * Real.sqrt 7) * rareMinimaxRisk μ ρ B

/-- The finite-cap factor is strictly below the published factor 8:
`3√7 R < 8R`, since the minimax risk is positive and finite. -/
def BelowEightStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    ENNReal.ofReal (3 * Real.sqrt 7) * rareMinimaxRisk μ ρ B < 8 * rareMinimaxRisk μ ρ B

end ThresholdHC.ProgramFactor
