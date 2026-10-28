import ThresholdHC.Tier6.AlgorithmModel

/-!
The unbiased converse uses the existing observable adaptive experiment.
Integrability is explicit in unbiasedness; variance and work are extended-real
quantities, so divergent values cannot disappear through `toReal`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC.Tier6

/-- Unbiasedness for the entire measurable sign class at a fixed gap law. -/
def UniformlyUnbiased {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) : Prop :=
  ∀ q : SignLaw, Integrable (populationOutput A) (experimentLaw μ A q) ∧
    (∫ z, populationOutput A z ∂experimentLaw μ A q) = signMean μ q.val

/-- A genuine uniform variance bound, including the possibility of infinite variance. -/
def UniformVarianceBound {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (V : ℝ) : Prop :=
  ∀ q : SignLaw, evariance (populationOutput A) (experimentLaw μ A q) ≤ ENNReal.ofReal V

end ThresholdHC.UnbiasedConverse
