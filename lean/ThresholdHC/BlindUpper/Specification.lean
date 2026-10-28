import ThresholdHC.Tier6.AlgorithmModel

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

/-- One budget-indexed family is selected before every magnitude law.
The existing experiment measures actual flips and retains infinite squared risk.
This is a specification only; no attaining construction is asserted here. -/
def DistributionBlindUpperStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
      ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        UniformBudget μ (rule B) B ∧
        maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (C*modulus μ (1/Real.sqrt B))

end ThresholdHC.BlindUpper
