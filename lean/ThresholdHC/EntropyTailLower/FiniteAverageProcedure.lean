import ThresholdHC.CriticalEntropy.RepeatedRestart
import ThresholdHC.CriticalEntropy.UniformCoin
import ThresholdHC.BlindUpper.ProductionAverage

/-! Actual independent finite averaging on successive unused flips of one coin.
The original work and second moment must be finite for the corresponding identities. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

def averageProcedure {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (n : ℕ) : StoppedProcedure (Fin (n+1) → R) ℝ :=
  postprocessProcedure (repeatedProcedure A (n+1)) (finiteAverage id n)
    (measurable_finiteAverage id measurable_id n)

theorem averageProcedure_work {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞) (n : ℕ) :
    expectedStoppedProcedureWork (Measure.pi (fun _ : Fin (n+1) => ν)) p (averageProcedure A n) =
      ((n:ℝ≥0∞)+1)*expectedStoppedProcedureWork ν p A := by
  change expectedStoppedProcedureWork _ _ (repeatedProcedure A (n+1)) = _
  simpa only [Nat.cast_add,Nat.cast_one] using repeated_expected_work ν p A hW (n+1)

theorem averageProcedure_output_law {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞) (n : ℕ) :
    ((Measure.pi (fun _ : Fin (n+1) => ν)).prod (tapeMeasure p)).map (averageProcedure A n).output =
      (Measure.pi (fun _ : Fin (n+1) => (ν.prod (tapeMeasure p)).map A.output)).map (finiteAverage id n) := by
  change ((Measure.pi (fun _ : Fin (n+1) => ν)).prod (tapeMeasure p)).map
    (finiteAverage id n ∘ (repeatedProcedure A (n+1)).output) = _
  rw [← Measure.map_map (measurable_finiteAverage id measurable_id n)
    (repeatedProcedure A (n+1)).measurable_output,repeated_output_map ν p A hW]

theorem averageProcedure_secondMoment_finite {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞)
    (hM : conditionalSecondMoment ν p A ≠ ∞) (n : ℕ) :
    conditionalSecondMoment (Measure.pi (fun _ : Fin (n+1) => ν)) p (averageProcedure A n) ≠ ∞ := by
  apply (conditionalSecondMoment_finite_iff _ _ _).mpr
  rw [averageProcedure_output_law ν p A hW n]
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (measurable_finiteAverage id measurable_id n).aemeasurable).mpr
  exact finiteAverage_memLp _ id ((conditionalSecondMoment_finite_iff ν p A).mp hM) n

theorem averageProcedure_mean {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞)
    (hM : conditionalSecondMoment ν p A ≠ ∞) (n : ℕ) :
    conditionalMean (Measure.pi (fun _ : Fin (n+1) => ν)) p (averageProcedure A n) =
      conditionalMean ν p A := by
  rw [← conditionalMean_output_law,averageProcedure_output_law ν p A hW n,
    integral_map (measurable_finiteAverage id measurable_id n).aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) _ from measurable_id.aestronglyMeasurable)]
  exact (finiteAverage_mean _ id ((conditionalSecondMoment_finite_iff ν p A).mp hM) n).trans
    (conditionalMean_output_law ν p A)

theorem averageProcedure_secondMoment_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hW : expectedStoppedProcedureWork ν p A ≠ ∞)
    (hM : conditionalSecondMoment ν p A ≠ ∞) (n : ℕ) :
    (conditionalSecondMoment (Measure.pi (fun _ : Fin (n+1) => ν)) p (averageProcedure A n)).toReal ≤
      (conditionalSecondMoment ν p A).toReal/((n:ℝ)+1)+(conditionalMean ν p A)^2 := by
  have hm := (conditionalSecondMoment_finite_iff ν p A).mp hM
  rw [← conditionalSecondMoment_output_law _ _ _ (averageProcedure_secondMoment_finite ν p A hW hM n),
    averageProcedure_output_law ν p A hW n,
    integral_map (measurable_finiteAverage id measurable_id n).aemeasurable
      (show Measurable (fun x : ℝ => x^2) by fun_prop).aestronglyMeasurable]
  have he := finiteAverage_mse _ id hm n 0
  simp only [sub_zero,id_eq] at he
  rw [he,conditionalMean_output_law ν p A]
  refine add_le_add ?_ le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← conditionalSecondMoment_output_law ν p A hM]
  exact variance_le_expectation_sq measurable_id.aestronglyMeasurable

end ThresholdHC.EntropyTailLower
