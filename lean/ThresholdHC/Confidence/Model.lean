import ThresholdHC.Tier6.AlgorithmModel

/-!
Confidence uses the original observable adaptive experiment and its expected
number of actual flips. The failure event is strict, as in the paper's radius
definition. No output is assumed bounded or square integrable.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6

def failureProbability {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) (r : ℝ) : ℝ≥0∞ :=
  (experimentLaw μ A q) {z | r < |populationOutput A z - signMean μ q.val|}

def UniformConfidence {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (r δ : ℝ) : Prop :=
  ∀ q : SignLaw, failureProbability μ A q r ≤ ENNReal.ofReal δ

/-- Infimum over all nonnegative attainable uniform radii and arbitrary
measurable seed spaces. The budget is uniform over the same sign class. -/
def minimaxConfidenceRadius (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B δ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (r : ℝ),
    0 ≤ r ∧ UniformBudget μ A B ∧ UniformConfidence μ A r δ ∧ t = ENNReal.ofReal r}

def confidenceScale (B δ : ℝ) : ℝ := Real.sqrt (Real.log (1/δ) / B)

end ThresholdHC.Confidence
