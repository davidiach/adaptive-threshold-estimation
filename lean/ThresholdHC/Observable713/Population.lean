import ThresholdHC.Observable713.Conditional
import ThresholdHC.BlindUpper.CallLaw

/-! Integrate the fixed-gap bounds under every measurable population sign law. -/

noncomputable section
namespace ThresholdHC.Observable713
open MeasureTheory ThresholdHC.Uniform713 ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem call_lintegral_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ)
    (F : ℕ × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ d s, (∫⁻ z, F z ∂levelMeasure.prod (Tier2.tapeMeasure (gapParameter s d))) ≤
      ENNReal.ofReal (C*(d : ℝ)⁻¹)) :
    (∫⁻ z, F z ∂callMeasure μ q) ≤ ENNReal.ofReal (C*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) := by
  have hp := populationInput_preserving μ levelMeasure (gapParameter false) (gapParameter true)
    (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  change (∫⁻ z, F z ∂levelMeasure.prod (originalPopulationTapeLaw μ q)) ≤ _
  unfold originalPopulationTapeLaw
  rw [← hp.lintegral_comp hF]
  unfold populationMeasure
  rw [population_lintegral μ levelMeasure _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q) F hF]
  calc
    _ ≤ ∫⁻ d : Gap, ENNReal.ofReal (C*(d : ℝ)⁻¹) ∂μ := lintegral_mono (fun d =>
      unit_mixture_bound (signUnit q d) _ (hb d true) (hb d false))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul C)
        (ae_of_all _ (fun d => mul_nonneg hC (inv_nonneg.mpr d.property.1.le))),integral_const_mul]

theorem call_second_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    (∫⁻ z, ENNReal.ofReal ((callValue z)^2) ∂callMeasure μ q) ≤
      ENNReal.ofReal (23*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) :=
  call_lintegral_bound μ q hI _ (measurable_callValue.pow_const 2).ennreal_ofReal 23
    (by norm_num) conditional_second_le

theorem call_work_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    (∫⁻ z, (callCost z : ℝ≥0∞) ∂callMeasure μ q) ≤
      ENNReal.ofReal (31*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) :=
  call_lintegral_bound μ q hI _
    ((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp measurable_callCost) 31
    (by norm_num) conditional_work_le

theorem call_memLp (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) : MemLp callValue 2 (callMeasure μ q) := by
  apply (memLp_two_iff_integrable_sq measurable_callValue.aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_callValue.pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun z => sq_nonneg _))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (call_second_le μ q hI)

theorem call_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    (∫ z, callValue z ∂callMeasure μ q) = signMean μ q.val := by
  have hp := populationInput_preserving μ levelMeasure (gapParameter false) (gapParameter true)
    (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  have hi := (call_memLp μ q hI).integrable (by norm_num)
  have hic := (hp.integrable_comp measurable_callValue.aestronglyMeasurable).mpr hi
  change (∫ z, callValue z ∂levelMeasure.prod (originalPopulationTapeLaw μ q)) = _
  unfold originalPopulationTapeLaw
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable measurable_callValue.aestronglyMeasurable]
  unfold populationMeasure
  rw [population_integral μ levelMeasure _ _ _ callValue measurable_callValue hic]
  change _ = ∫ d, q.val d ∂μ
  apply integral_congr_ae
  filter_upwards [] with d
  have h₁ := (conditional_call d true).2.2.2.2
  have h₀ := (conditional_call d false).2.2.2.2
  change (q.val d)*(∫ z, callValue z ∂samplingMeasure (Tier2.tapeMeasure (gapParameter true d))) +
    (1-q.val d)*(∫ z, callValue z ∂samplingMeasure (Tier2.tapeMeasure (gapParameter false d))) = _
  rw [h₁,h₀]
  simp [signValue]

end ThresholdHC.Observable713
