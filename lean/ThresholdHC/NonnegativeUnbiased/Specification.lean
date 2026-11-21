import ThresholdHC.UnbiasedConverse.Model

/-! Target statement for the first sentence of Proposition prop:bounded (v6 §6):
when some gaps lie below `1/2`, no algorithm that stops almost surely and returns
an almost surely nonnegative value under every sign law is unbiased on the
whole sign class. The second sentence, the endpoint gap `1/2`, is
`PaperStatements.HalfGapUnbiasedStatement`. The proof is in `Support.lean`. -/
noncomputable section
namespace ThresholdHC.NonnegativeUnbiased
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.UnbiasedConverse
open scoped ENNReal

/-- If `μ((0,1/2)) > 0`, no algorithm that stops almost surely and has almost
surely nonnegative output under every measurable sign law is unbiased for
every measurable sign law. -/
def NonnegativeUnbiasedStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R),
    0 < μ {d : Gap | (d : ℝ) < 1/2} →
    (∀ q : SignLaw, ∀ᵐ z ∂experimentLaw μ A q,
      ∃ n, A.policy z.1.1 (processHistory z.2 n) = none) →
    (∀ q : SignLaw, ∀ᵐ z ∂experimentLaw μ A q, 0 ≤ populationOutput A z) →
    ¬ UniformlyUnbiased μ A

end ThresholdHC.NonnegativeUnbiased
