import ThresholdHC.Observable713.Classifier
import ThresholdHC.Uniform713.Conditional
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Instantiate the existing 713 analysis with actual iid Bernoulli flips. -/

noncomputable section
namespace ThresholdHC.Observable713
open MeasureTheory ThresholdHC.Uniform713 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem conditional_call (d : Gap) (s : Bool) :
    MemLp callValue 2 (samplingMeasure (Tier2.tapeMeasure (gapParameter s d))) ∧
    Integrable (fun z => (callCost z : ℝ)) (samplingMeasure (Tier2.tapeMeasure (gapParameter s d))) ∧
    (∫ z, (callValue z)^2 ∂samplingMeasure (Tier2.tapeMeasure (gapParameter s d))) < 23/(d : ℝ) ∧
    (∫ z, (callCost z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (gapParameter s d))) < 31/(d : ℝ) ∧
    (∫ z, callValue z ∂samplingMeasure (Tier2.tapeMeasure (gapParameter s d))) = signValue s := by
  have ht : HasMeanTails (Tier2.tapeMeasure (gapParameter s d))
      (dyadicMean Tier2.observations) (coinMean d s) := by
    convert Tier2.tape_mean_tails (gapParameter s d) using 1
    cases s <;> simp [coinMean,gapParameter,sub_eq_add_neg]
  unfold callValue
  simp_rw [callCost_eq_work]
  exact conditional_bounds (Tier2.tapeMeasure (gapParameter s d)) Tier2.observations d s
    d.property.1 d.property.2 ht

theorem conditional_second_le (d : Gap) (s : Bool) :
    (∫⁻ z, ENNReal.ofReal ((callValue z)^2)
      ∂levelMeasure.prod (Tier2.tapeMeasure (gapParameter s d))) ≤ ENNReal.ofReal (23*(d : ℝ)⁻¹) := by
  have h := conditional_call d s
  unfold samplingMeasure at h
  rw [← ofReal_integral_eq_lintegral_ofReal h.1.integrable_sq
    (ae_of_all _ (fun z => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (by simpa only [div_eq_mul_inv] using h.2.2.1.le)

theorem conditional_work_le (d : Gap) (s : Bool) :
    (∫⁻ z, (callCost z : ℝ≥0∞)
      ∂levelMeasure.prod (Tier2.tapeMeasure (gapParameter s d))) ≤ ENNReal.ofReal (31*(d : ℝ)⁻¹) := by
  have h := conditional_call d s
  unfold samplingMeasure at h
  have he : (fun z => (callCost z : ℝ≥0∞)) = fun z => ENNReal.ofReal (callCost z : ℝ) := by
    funext z
    simp
  rw [he,← ofReal_integral_eq_lintegral_ofReal h.2.1
    (ae_of_all _ (fun z => Nat.cast_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (by simpa only [div_eq_mul_inv] using h.2.2.2.1.le)

end ThresholdHC.Observable713
