import ThresholdHC.UnbiasedConverse.Model

noncomputable section
open MeasureTheory
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC.Tier6

/-- Theorem 2's converse and sharp universal lower coefficient. The algorithm
may use any measurable seed space, create arbitrarily many coins, and revisit
or interleave them. No information bound or differentiability hypothesis is
part of the specification. -/
def UnbiasedConverseStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (V W : ℝ),
    0 ≤ V → 0 ≤ W → UniformlyUnbiased μ A →
    UniformVarianceBound μ A V → UniformBudget μ A W →
    Integrable (fun d : Gap => (d : ℝ)⁻¹) μ ∧
      (∫ d : Gap, (d : ℝ)⁻¹ ∂μ)^2 / 16 ≤ V * W

end ThresholdHC.UnbiasedConverse
