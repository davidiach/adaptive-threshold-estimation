import ThresholdHC.BlindUpper.PopulationMean

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

def callMeasure (μ : Measure Gap) (q : SignLaw) : Measure (ℕ × (ℕ → Bool)) :=
  levelMeasure.prod (originalPopulationTapeLaw μ q)

instance callMeasure_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (callMeasure μ q) := by unfold callMeasure; infer_instance

theorem cutoff_call_second_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, ENNReal.ofReal ((cutoffValue L z)^2) ∂callMeasure μ q) ≤
      ENNReal.ofReal (85*∫ d, callScale L d ∂μ) := by
  have he := (populationInput_preserving μ levelMeasure (gapParameter false) (gapParameter true)
    (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
    (measurable_signUnit q)).lintegral_comp
      (ENNReal.measurable_ofReal.comp ((measurable_cutoffValue L).pow_const 2))
  exact he ▸ cutoff_population_second_le L μ q

theorem cutoff_call_sq_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    Integrable (fun z => (cutoffValue L z)^2) (callMeasure μ q) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_cutoffValue L).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun z => sq_nonneg _))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (cutoff_call_second_le L μ q)

theorem cutoff_call_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    Integrable (cutoffValue L) (callMeasure μ q) :=
  ((memLp_two_iff_integrable_sq (measurable_cutoffValue L).aestronglyMeasurable).mpr
    (cutoff_call_sq_integrable L μ q)).integrable (by norm_num)

theorem cutoff_call_second_real_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (cutoffValue L z)^2 ∂callMeasure μ q) ≤ 85*∫ d, callScale L d ∂μ := by
  have hb := cutoff_call_second_le L μ q
  rw [← ofReal_integral_eq_lintegral_ofReal (cutoff_call_sq_integrable L μ q)
    (ae_of_all _ (fun z => sq_nonneg _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
    (integral_nonneg (fun d => (callScale_bounds L d).1)))).mp hb

theorem cutoff_call_mean (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, cutoffValue L z ∂callMeasure μ q) =
      populationMean μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
        (cutoffProcedure L) := by
  have hp := populationInput_preserving μ levelMeasure (gapParameter false) (gapParameter true)
    (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
    (measurable_signUnit q)
  change (∫ z, cutoffValue L z ∂levelMeasure.prod (originalPopulationTapeLaw μ q)) = _
  unfold originalPopulationTapeLaw
  rw [← hp.map_eq]
  exact integral_map hp.measurable.aemeasurable (measurable_cutoffValue L).aestronglyMeasurable

theorem cutoff_call_bias_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    |(∫ z, cutoffValue L z ∂callMeasure μ q)-signMean μ q.val| ≤
      ∫ d, callBiasScale L d ∂μ := by
  rw [cutoff_call_mean]
  exact cutoff_population_bias_le L μ q

theorem cutoff_call_cost_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    Integrable (fun z => (cutoffCost L z : ℝ)) (callMeasure μ q) := by
  have hm : Measurable (fun z => (cutoffCost L z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_cutoffCost L)
  apply Integrable.of_bound hm.aestronglyMeasurable ((2 : ℝ)^L)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast cutoffCost_le L z)

theorem cutoff_call_work_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, stoppedProcedureWork (cutoffProcedure L) z ∂callMeasure μ q) ≤
      ENNReal.ofReal (149*∫ d, callScale L d ∂μ) := by
  unfold callMeasure originalPopulationTapeLaw
  rw [← populationInput_work μ levelMeasure (gapParameter false) (gapParameter true)
    (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
    (measurable_signUnit q) (cutoffProcedure L)]
  exact cutoff_population_work_le L μ q

theorem cutoff_call_work_real (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    ENNReal.ofReal (∫ z, (cutoffCost L z : ℝ) ∂callMeasure μ q) =
      ∫⁻ z, stoppedProcedureWork (cutoffProcedure L) z ∂callMeasure μ q := by
  rw [ofReal_integral_eq_lintegral_ofReal (cutoff_call_cost_integrable L μ q)
    (ae_of_all _ (fun z => Nat.cast_nonneg _))]
  apply lintegral_congr
  intro z
  simp [stoppedProcedureWork,cutoffProcedure,finiteStoppedProcedure]

theorem cutoff_call_work_real_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (cutoffCost L z : ℝ) ∂callMeasure μ q) ≤ 149*∫ d, callScale L d ∂μ := by
  have hb := cutoff_call_work_le L μ q
  rw [← cutoff_call_work_real] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
    (integral_nonneg (fun d => (callScale_bounds L d).1)))).mp hb

theorem cutoff_call_work_pos (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    0 < ∫ z, (cutoffCost L z : ℝ) ∂callMeasure μ q := by
  have hf : Measurable (fun z : ℕ × (ℕ → Bool) =>
      ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) z.1) :=
    (measurable_const.indicator (measurableSet_singleton 0)).comp measurable_fst
  have hlow := lintegral_mono (μ := callMeasure μ q)
    (f := fun z : ℕ × (ℕ → Bool) => ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) z.1)
    (g := fun z => stoppedProcedureWork (cutoffProcedure L) z) (fun z => by
      by_cases hz : z.1 = 0
      · simp only [Set.indicator_apply,Set.mem_singleton_iff,hz,ite_true]
        have hez : z = (0,z.2) := Prod.ext hz rfl
        rw [hez]
        simp [stoppedProcedureWork,cutoffProcedure,finiteStoppedProcedure,cutoff_zero_level_cost]
      · simp [Set.indicator_apply,hz])
  have he : (∫⁻ z : ℕ × (ℕ → Bool),
      ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) z.1 ∂callMeasure μ q) =
      ENNReal.ofReal (levelProb 0) := by
    rw [callMeasure,lintegral_prod _ hf.aemeasurable]
    simp only [lintegral_const,measure_univ,mul_one]
    rw [lintegral_indicator_fun_one (measurableSet_singleton 0),levelMeasure_singleton]
  rw [he,← cutoff_call_work_real] at hlow
  exact ENNReal.ofReal_pos.mp ((ENNReal.ofReal_pos.mpr (levelProb_pos 0)).trans_le hlow)


end ThresholdHC.BlindUpper
