import ThresholdHC.Tier6.AlgorithmModel

/-! Target statements for the upper constant 15 of the RMS law. They use only
the original experiment, budget, risk and modulus definitions. The proofs are
in the other modules of this directory. -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

/-- One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 15 times the modulus. -/
def BlindUpper15Statement : Prop :=
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (15*modulus μ (1/Real.sqrt B))

/-- The minimax RMS risk is at most 15 times the modulus. -/
def MinimaxUpper15Statement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (15*modulus μ (1/Real.sqrt B))

end ThresholdHC.UpperSign
