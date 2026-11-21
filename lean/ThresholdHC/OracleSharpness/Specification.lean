import ThresholdHC.OracleLower.Model
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Target statements for the sharpness of the oracle upper coefficient one
half. Source: research/2026-11-17-rms-constants/adaptive-threshold-second-review.tex,
section Sharpness and an unbiased one-flip estimator, paragraph Sharp upper
coefficient for the oracles (line 83 at the time of writing; the file has no
LaTeX labels). Fix a budget at least one and let the gap of a point-mass law
decrease to zero. The source concludes that the liminf of the oracle risk
is at least one half while the modulus at the inverse square root of the
budget equals one. The first target states this eventual bound for every
coefficient below one half and for both magnitude oracles. The second target
is an auxiliary ordinary-model bound used in the proof; it is not a claim of
the source. The upper bound itself, R at most one half of the modulus, is not
stated here. -/
noncomputable section
namespace ThresholdHC.OracleSharpness
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- Eventual form of the source's limit along point masses: for every budget
at least one and every coefficient below one half, all point masses at
sufficiently small gaps have both oracle minimax risks strictly above that coefficient
times the modulus at the inverse square root of the budget. -/
def OracleUpperSharpnessStatement : Prop :=
  ∀ (B c : ℝ), 1 ≤ B → c < 1/2 → ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g : Gap, g.val ≤ g₀ →
    ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) * c) <
      revealedMinimaxRisk (Measure.dirac g) B ∧
    ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) * c) <
      selectedMinimaxRisk (Measure.dirac g) B

/-- Auxiliary ordinary-model bound, not a claim of the source. For a point
mass at a gap `g` with flip bias `s = 2g` below one, a nonnegative budget `B`
and a nonnegative `c`, the single-gap minimax risk is at least `c` whenever
`s · artanh s · B ≤ 1 - 4c²`. -/
def SmallGapSignLowerStatement : Prop :=
  ∀ (g : Gap) (B c : ℝ), 0 ≤ B → 0 ≤ c → 2 * g.val < 1 →
    2 * g.val * Real.artanh (2 * g.val) * B ≤ 1 - 4 * c^2 →
    ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B

end ThresholdHC.OracleSharpness
