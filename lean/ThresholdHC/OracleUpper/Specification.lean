import ThresholdHC.OracleLower.Model

/-! Target statements for the upper bound of the two magnitude-oracle minimax
risks by one half of the modulus. Source:
research/2026-11-17-rms-constants/adaptive-threshold-second-review.tex, section
on the exact large-budget constant for magnitude oracles, paragraphs An
estimator for both oracles and Finite budgets, every gap law (lines 63-77 at
the time of writing; the file has no LaTeX labels). With n the floor of a
budget B at least one and a = 1/(2 sqrt n), the source bounds the oracle RMS
risk by one half of the modulus at a, and then by one half of the modulus at
B^(-1/2), for every gap law. The first target is the second form and the
second target is the floor form. The third target says that one half is
exactly the best universal coefficient for either oracle; its lower half is
the sharpness paragraph Sharp upper coefficient for the oracles (line 83),
which the audited group ThresholdHC.OracleSharpness already proves and which
is not restated here. -/
noncomputable section
namespace ThresholdHC.OracleUpper
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- For every gap law and every budget at least one, both magnitude-oracle
minimax RMS risks are at most one half of the modulus at B^(-1/2). -/
def OracleUpperStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    revealedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 2) ∧
    selectedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 2)

/-- The finite-budget form at the smaller scale 1/(2 sqrt n), with n the
floor of the budget. -/
def OracleFloorUpperStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    revealedMinimaxRisk μ B ≤
      ENNReal.ofReal (modulus μ (1 / (2 * Real.sqrt (Nat.floor B : ℝ))) / 2) ∧
    selectedMinimaxRisk μ B ≤
      ENNReal.ofReal (modulus μ (1 / (2 * Real.sqrt (Nat.floor B : ℝ))) / 2)

/-- One half is the smallest coefficient of the modulus at B^(-1/2) that
bounds either oracle minimax risk at every gap law and every budget at least
one. -/
def OracleUpperCoefficientStatement : Prop :=
  ∀ c : ℝ,
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
        revealedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c)) ↔
      1/2 ≤ c) ∧
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
        selectedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c)) ↔
      1/2 ≤ c)

end ThresholdHC.OracleUpper
