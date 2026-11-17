import SharpOracleAttainment

open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.OracleLower ThresholdHC.SharpRMS

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ selectedMinimaxRisk μ B := @oracle_minimax_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ selectedMinimaxRisk μ B := @oracle_large_budget_lower

example : revealedMinimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) ∧
    selectedMinimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) := oracle_endpoint_eq

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : OracleEstimator R) (B : ℝ), OracleBudget A B →
    ENNReal.ofReal (modulus μ g.val)*minimaxRisk (Measure.dirac g) B ≤ oracleRisk μ A := @oracle_gap_reduction

#print axioms oracle_minimax_lower
#print axioms oracle_large_budget_lower
#print axioms oracle_endpoint_eq
#print axioms oracle_gap_reduction
