import ThresholdHC.Tier6.AlgorithmModel

/-! Adding a deterministic offset preserves the observable experiment and
expected work, and translates the target in squared risk. -/

noncomputable section
open MeasureTheory
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6

def shiftEstimator {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (c : ℝ) : AdaptiveEstimator R :=
  { A with output := fun z => c+A.output z, output_measurable := measurable_const.add A.output_measurable }

theorem shiftEstimator_experiment {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (c : ℝ) :
    experimentLaw μ (shiftEstimator A c) q = experimentLaw μ A q := rfl

theorem shiftEstimator_work {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (c : ℝ) :
    expectedWork μ (shiftEstimator A c) q = expectedWork μ A q := rfl

theorem shiftEstimator_squaredRisk {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (c a : ℝ) :
    squaredRisk (experimentLaw μ (shiftEstimator A c) q) (populationOutput (shiftEstimator A c)) a =
      squaredRisk (experimentLaw μ A q) (populationOutput A) (a-c) := by
  rw [shiftEstimator_experiment]
  apply lintegral_congr
  intro z
  congr 1
  change (c+populationOutput A z-a)^2 = (populationOutput A z-(a-c))^2
  ring

end ThresholdHC.StoppingProgram
