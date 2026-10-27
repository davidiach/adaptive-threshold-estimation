import ThresholdHC.CriticalEntropy.RepeatedSignModel
import ThresholdHC.CriticalEntropy.RepeatedRestart
import ThresholdHC.CriticalEntropy.SampleMean

/-!
Transfer the finite-product error bounds to the actual repeated sign test.
The hypotheses describe the single procedure's output distribution at a fixed
Bernoulli parameter; iid restarts and honest work are proved conclusions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem repeated_sign_work {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞)
    (n : ℕ) (t : ℝ) :
    expectedSignTestWork (Measure.pi (fun _ : Fin n => ν)) p (repeatedSignTest A n t) =
      (n : ℝ≥0∞) * expectedStoppedProcedureWork ν p A :=
  repeated_expected_work ν p A hfinite n

theorem repeated_sign_plus_error {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞)
    (h : MemLp id 2 ((ν.prod (Tier2.tapeMeasure p)).map A.output))
    (n : ℕ) (hn : 0 < n) (a M t : ℝ) (ha : 0 < a)
    (hM : (∫ x : ℝ, x^2 ∂(ν.prod (Tier2.tapeMeasure p)).map A.output) ≤ M)
    (hm : t+a ≤ ∫ x : ℝ, x ∂(ν.prod (Tier2.tapeMeasure p)).map A.output) :
    ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).real
        {z | (repeatedSignTest A n t).output z ≠ true} ≤ M / ((n : ℝ)*a^2) := by
  have hs : MeasurableSet {x | repeatedSignDecision n t x ≠ true} :=
    (measurableSet_eq_fun (measurable_repeatedSignDecision n t) measurable_const).compl
  change ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).real
      ((repeatedProcedure A n).output ⁻¹' {x | repeatedSignDecision n t x ≠ true}) ≤ _
  rw [← map_measureReal_apply (repeatedProcedure A n).measurable_output hs,
    repeated_output_map ν p A hfinite n]
  simpa [repeatedSignDecision] using iid_sum_lower_error _ h n hn a M t ha hM hm

theorem repeated_sign_minus_error {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞)
    (h : MemLp id 2 ((ν.prod (Tier2.tapeMeasure p)).map A.output))
    (n : ℕ) (hn : 0 < n) (a M t : ℝ) (ha : 0 < a)
    (hM : (∫ x : ℝ, x^2 ∂(ν.prod (Tier2.tapeMeasure p)).map A.output) ≤ M)
    (hm : (∫ x : ℝ, x ∂(ν.prod (Tier2.tapeMeasure p)).map A.output)+a ≤ t) :
    ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).real
        {z | (repeatedSignTest A n t).output z ≠ false} ≤ M / ((n : ℝ)*a^2) := by
  have hs : MeasurableSet {x | repeatedSignDecision n t x ≠ false} :=
    (measurableSet_eq_fun (measurable_repeatedSignDecision n t) measurable_const).compl
  change ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).real
      ((repeatedProcedure A n).output ⁻¹' {x | repeatedSignDecision n t x ≠ false}) ≤ _
  rw [← map_measureReal_apply (repeatedProcedure A n).measurable_output hs,
    repeated_output_map ν p A hfinite n]
  simpa only [repeatedSignDecision, ne_eq, ite_eq_right_iff, Bool.true_eq_false,
    imp_false, not_not] using iid_sum_upper_error _ h n hn a M t ha hM hm

end ThresholdHC.CriticalEntropy
