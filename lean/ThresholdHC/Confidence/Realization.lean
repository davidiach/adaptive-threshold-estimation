import ThresholdHC.Confidence.Pointwise
import ThresholdHC.Confidence.SingleFailure
import ThresholdHC.Confidence.Model

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

abbrev CalibrationArray := ℕ → CalibrationState (ℕ × (ℕ → Bool))

def calibrationArrayLaw (μ : Measure Gap) (q : SignLaw) : Measure CalibrationArray :=
  Measure.infinitePi (fun _ : ℕ => calibrationLaw (callMeasure μ q))

theorem calibrationEval_preserving (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (i : ℕ) :
    MeasurePreserving (fun x : CalibrationArray => x i) (calibrationArrayLaw μ q)
      (calibrationLaw (callMeasure μ q)) :=
  ⟨measurable_pi_apply i,Measure.infinitePi_map_eval _ i⟩

theorem repeat_uniformBudget (m L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    UniformBudget μ (repeatEstimator m L) ((2*m+1 : ℕ)*(4*(2 : ℝ)^L)) := by
  intro q
  rw [original_expectedWork_simulation]
  calc
    _ = ∫⁻ z, ∑ i : MedianIndex m, cutoffBatchWork L (calibrationInputs z i.val)
        ∂originalSimulationLaw μ (repeatEstimator m L) q := by
      apply lintegral_congr_ae
      filter_upwards [repeat_population_identities m L μ q] with z hz
      exact hz.1
    _ = ∑ i : MedianIndex m, ∫⁻ z, cutoffBatchWork L (calibrationInputs z i.val)
        ∂originalSimulationLaw μ (repeatEstimator m L) q :=
      lintegral_finsetSum _ (fun i _ => (measurable_cutoffBatchWork L).comp
        ((measurable_pi_apply i.val).comp measurable_calibrationInputs))
    _ = ∑ _i : MedianIndex m, ∫⁻ z, cutoffBatchWork L z ∂calibrationLaw (callMeasure μ q) := by
      apply Finset.sum_congr rfl
      intro i _
      exact ((batchInput_preserving μ q).comp (repeatInput_preserving m L i.val μ q)).lintegral_comp
        (measurable_cutoffBatchWork L)
    _ ≤ ∑ _i : MedianIndex m, ENNReal.ofReal (4*(2 : ℝ)^L) :=
      Finset.sum_le_sum (fun _ _ => cutoffBatch_budget L μ q)
    _ = _ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
      simp [nsmul_eq_mul]

theorem original_output_event {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (experimentLaw μ A q) {z | populationOutput A z ∈ s} =
      (originalSimulationLaw μ A q) {z | A.output (z.1,populationPath (A.policy z.1) z.2) ∈ s} := by
  have hset := hs.preimage A.output_measurable
  have hm : Measurable (fun z : R × (ℕ → ℕ → Bool) => (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  have hm₀ : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h := congrArg (fun M : Measure (R × ProcessTape) => M (A.output ⁻¹' s))
    (original_observable_simulation_law μ A q)
  rw [Measure.map_apply hm₀ hset,Measure.map_apply hm hset] at h
  exact h

theorem repeat_failure_eq (m L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (r : ℝ) :
    failureProbability μ (repeatEstimator m L) q r =
      (calibrationArrayLaw μ q) {x | r < |median m (fun i => cutoffBatchOutput L (x i.val))-signMean μ q.val|} := by
  have hs : MeasurableSet {x : ℝ | r < |x-signMean μ q.val|} :=
    measurableSet_lt measurable_const ((measurable_id.sub_const _).abs)
  unfold failureProbability
  calc
    _ = (originalSimulationLaw μ (repeatEstimator m L) q)
        {z | r < |repeatOutput m L (z.1,populationPath (repeatPolicy m L z.1) z.2)-signMean μ q.val|} :=
      original_output_event μ (repeatEstimator m L) q _ hs
    _ = (originalSimulationLaw μ (repeatEstimator m L) q)
        {z | r < |median m (fun i => cutoffBatchOutput L (calibrationInputs z i.val))-signMean μ q.val|} := by
      apply measure_congr
      filter_upwards [repeat_population_identities m L μ q] with z hz
      rw [hz.2]
    _ = _ := by
      have hset : MeasurableSet {x : CalibrationArray | r <
          |median m (fun i => cutoffBatchOutput L (x i.val))-signMean μ q.val|} :=
        measurableSet_lt measurable_const
        (((measurable_median m _ (fun i => (measurable_cutoffBatchOutput L).comp
          (measurable_pi_apply i.val))).sub_const _).abs)
      exact (calibrationInputs_preserving m L μ q).measure_preimage hset.nullMeasurableSet

theorem repeat_failure_le (m L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    failureProbability μ (repeatEstimator m L) q (512*modulus μ (1/Real.sqrt ((2 : ℝ)^L))) ≤
      (1/2 : ℝ≥0∞)^m := by
  rw [repeat_failure_eq]
  have hind : iIndepFun (fun i : ℕ => fun x : CalibrationArray => cutoffBatchOutput L (x i))
      (calibrationArrayLaw μ q) := iIndepFun_infinitePi (fun _ => measurable_cutoffBatchOutput L)
  apply median_failure_bound _ m _ (hind.precomp Fin.val_injective)
  intro i
  have hs : MeasurableSet {z | 512*modulus μ (1/Real.sqrt ((2 : ℝ)^L)) <
      |cutoffBatchOutput L z-signMean μ q.val|} :=
    measurableSet_lt measurable_const (((measurable_cutoffBatchOutput L).sub_const _).abs)
  calc
    _ = (calibrationLaw (callMeasure μ q)) {z | 512*modulus μ (1/Real.sqrt ((2 : ℝ)^L)) <
        |cutoffBatchOutput L z-signMean μ q.val|} :=
      (calibrationEval_preserving μ q i.val).measure_preimage hs.nullMeasurableSet
    _ ≤ _ := cutoffBatch_failure L μ q

end ThresholdHC.Confidence
