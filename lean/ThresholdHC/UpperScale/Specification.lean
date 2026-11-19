import ThresholdHC.Tier6.AlgorithmModel

/-! Target statements for the upper constant 12 of the RMS law. They use only
the original experiment, budget, risk and modulus definitions. The proofs are
in the other modules of this directory. -/
noncomputable section
namespace ThresholdHC.UpperScale
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

/-- One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 12 times the modulus. -/
def BlindUpper12Statement : Prop :=
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (12*modulus μ (1/Real.sqrt B))

/-- The minimax RMS risk is at most 12 times the modulus. -/
def MinimaxUpper12Statement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (12*modulus μ (1/Real.sqrt B))

end ThresholdHC.UpperScale
