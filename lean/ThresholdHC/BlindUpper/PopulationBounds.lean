import ThresholdHC.BlindUpper.CutoffBiasWork
import ThresholdHC.ObservableSimulation.OriginalExperiment
import ThresholdHC.CriticalEntropy.PopulationMixture
import ThresholdHC.CriticalEntropy.PopulationLocalWork

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

def callScale (L : ℕ) (d : Gap) : ℝ := min (Real.sqrt ((2 : ℝ)^L)) (d : ℝ)⁻¹

def callBiasScale (L : ℕ) (d : Gap) : ℝ := min 1 ((((2 : ℝ)^L*(d : ℝ)^2)⁻¹)^2)

theorem callScale_bounds (L : ℕ) (d : Gap) : 0 ≤ callScale L d ∧ callScale L d ≤ Real.sqrt ((2 : ℝ)^L) :=
  ⟨le_min (Real.sqrt_nonneg _) (inv_nonneg.mpr d.property.1.le),min_le_left _ _⟩

theorem callScale_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    Integrable (callScale L) μ := by
  have hm : Measurable (callScale L) := measurable_const.min measurable_subtype_coe.inv
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.sqrt ((2 : ℝ)^L))
  exact ae_of_all _ (fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg (callScale_bounds L d).1]
    exact (callScale_bounds L d).2)

theorem cutoff_conditional_second (L : ℕ) (p : unitInterval) :
    conditionalSecondMoment levelMeasure p (cutoffProcedure L) =
      ENNReal.ofReal (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure p)) := by
  exact (ofReal_integral_eq_lintegral_ofReal (cutoff_sq_integrable L p)
    (ae_of_all _ (fun z => sq_nonneg (cutoffValue L z)))).symm

theorem cutoff_conditional_second_le (L : ℕ) (d : Gap) (S : Bool) :
    conditionalSecondMoment levelMeasure (gapParameter S d) (cutoffProcedure L) ≤
      ENNReal.ofReal (85*callScale L d) := by
  rw [cutoff_conditional_second]
  exact ENNReal.ofReal_le_ofReal (cutoff_secondMoment_le L d S d.property.1 d.property.2)

theorem cutoff_conditional_work_le (L : ℕ) (d : Gap) (S : Bool) :
    expectedStoppedProcedureWork levelMeasure (gapParameter S d) (cutoffProcedure L) ≤
      ENNReal.ofReal (149*callScale L d) :=
  cutoff_expected_work_le L d S d.property.1 d.property.2

theorem unit_mixture_bound (q : unitInterval) {a b : ℝ≥0∞} (C : ℝ)
    (ha : a ≤ ENNReal.ofReal C) (hb : b ≤ ENNReal.ofReal C) :
    ENNReal.ofReal (q : ℝ)*a + ENNReal.ofReal (1-(q : ℝ))*b ≤ ENNReal.ofReal C := by
  calc
    _ ≤ ENNReal.ofReal (q : ℝ)*ENNReal.ofReal C +
        ENNReal.ofReal (1-(q : ℝ))*ENNReal.ofReal C :=
      add_le_add (mul_le_mul' le_rfl ha) (mul_le_mul' le_rfl hb)
    _ = _ := by
      rw [← add_mul,← ENNReal.ofReal_add q.property.1 (sub_nonneg.mpr q.property.2)]
      simp

theorem cutoff_population_second_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    populationSecondMoment μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
      (cutoffProcedure L) ≤ ENNReal.ofReal (85*∫ d, callScale L d ∂μ) := by
  rw [population_second_moment_formula μ levelMeasure _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal (85*callScale L d) ∂μ := lintegral_mono (fun d =>
      unit_mixture_bound (signUnit q d) _ (cutoff_conditional_second_le L d true)
        (cutoff_conditional_second_le L d false))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal ((callScale_integrable L μ).const_mul 85)
        (ae_of_all _ (fun d => mul_nonneg (by norm_num) (callScale_bounds L d).1)),integral_const_mul]

theorem cutoff_population_work_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    populationExpectedWork μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
      (cutoffProcedure L) ≤ ENNReal.ofReal (149*∫ d, callScale L d ∂μ) := by
  rw [population_work_formula μ levelMeasure _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal (149*callScale L d) ∂μ := lintegral_mono (fun d =>
      unit_mixture_bound (signUnit q d) _ (cutoff_conditional_work_le L d true)
        (cutoff_conditional_work_le L d false))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal ((callScale_integrable L μ).const_mul 149)
        (ae_of_all _ (fun d => mul_nonneg (by norm_num) (callScale_bounds L d).1)),integral_const_mul]

end ThresholdHC.BlindUpper
