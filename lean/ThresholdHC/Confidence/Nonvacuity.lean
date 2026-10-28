import ThresholdHC.Confidence.Specification
import ThresholdHC.Tier6.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6

theorem immediate_confidence (μ : Measure Gap) [IsProbabilityMeasure μ] (δ : ℝ) :
    UniformConfidence μ immediateEstimator 1 δ := by
  intro q
  have hm := signMean_bounds μ q
  have he : {z | (1 : ℝ) < |populationOutput immediateEstimator z - signMean μ q.val|} = ∅ := by
    ext z
    simp only [populationOutput, immediateEstimator, zero_sub, abs_neg,
      abs_of_nonneg hm.1, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact not_lt_of_ge hm.2
  unfold failureProbability
  rw [he, measure_empty]
  exact bot_le

theorem confidence_nonvacuity : ConfidenceNonvacuityStatement := by
  intro μ _ B δ hB hδ
  have hb : UniformBudget μ immediateEstimator B := by
    intro q
    rw [immediate_expectedWork_zero population_realization]
    exact bot_le
  have hc := immediate_confidence μ δ
  refine ⟨⟨immediateEstimator, hb, hc⟩, ?_⟩
  change sInf _ ≤ 1
  apply sInf_le
  exact ⟨Unit, inferInstance, immediateEstimator, 1, by norm_num, hb, hc, by simp⟩

end ThresholdHC.Confidence
