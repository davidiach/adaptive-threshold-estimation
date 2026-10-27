import ThresholdHC.CriticalEntropy.ObservationModel
import ThresholdHC.CriticalEntropy.PopulationGeometryModel
import ThresholdHC.CriticalEntropy.FiniteGeometryModel
import ThresholdHC.CriticalEntropy.GoodGapModel

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- The target is a separate coordinate: the observation probabilities need
not identify the positive fraction. -/
def cappedObservationVector {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R E) (m : ℕ) : Option (Fin (m+1) × Fin (m+1)) → ℝ
  | none => ∫ d, (q d : ℝ) ∂μ
  | some i => (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i}

/-- The image of every actual admissible population, not a postulated convex
set of probability vectors. -/
def cappedObservationImage {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ : D → unitInterval)
    (A : StoppedProcedure R E) (m : ℕ) (ρ : ℝ) :
    Set (Option (Fin (m+1) × Fin (m+1)) → ℝ) :=
  {v | ∃ q : D → unitInterval, CappedPrior μ ρ q ∧ cappedObservationVector μ ν p₀ p₁ q A m = v}

end ThresholdHC.CriticalEntropy
