import ThresholdHC.BlindUpper.PopulationBounds

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem callBiasScale_bounds (L : ℕ) (d : Gap) :
    0 ≤ callBiasScale L d ∧ callBiasScale L d ≤ 1 :=
  ⟨le_min (by norm_num) (sq_nonneg _),min_le_left _ _⟩

theorem callBiasScale_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    Integrable (callBiasScale L) μ := by
  have hm : Measurable (callBiasScale L) :=
    measurable_const.min ((measurable_const.mul (measurable_subtype_coe.pow_const 2)).inv.pow_const 2)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg (callBiasScale_bounds L d).1]
    exact (callBiasScale_bounds L d).2)

theorem cutoff_conditional_mean_bounds (L : ℕ) (p : unitInterval) :
    0 ≤ conditionalMean levelMeasure p (cutoffProcedure L) ∧
      conditionalMean levelMeasure p (cutoffProcedure L) ≤ 1 := by
  change 0 ≤ (∫ z, cutoffValue L z ∂samplingMeasure (Tier2.tapeMeasure p)) ∧
    (∫ z, cutoffValue L z ∂samplingMeasure (Tier2.tapeMeasure p)) ≤ 1
  rw [cutoff_mean]
  have hb (ω : ℕ → Bool) : 0 ≤ classifierValue L ω ∧ classifierValue L ω ≤ 1 := by
    rcases Tier2.Model.decision_zero_or_one (fun k => dyadicMean Tier2.observations k ω) L with h | h
    · simp only [classifierValue,h]; norm_num
    · simp only [classifierValue,h]; norm_num
  have hi : Integrable (classifierValue L) (Tier2.tapeMeasure p) := by
    apply Integrable.of_bound (measurable_classifierValue L).aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb ω).1]; exact (hb ω).2)
  exact ⟨integral_nonneg (fun ω => (hb ω).1),
    by simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun ω => (hb ω).2)⟩

def callMean (L : ℕ) (q : SignLaw) (d : Gap) : ℝ :=
  q.val d * conditionalMean levelMeasure (gapParameter true d) (cutoffProcedure L) +
    (1-q.val d) * conditionalMean levelMeasure (gapParameter false d) (cutoffProcedure L)

theorem measurable_callMean (L : ℕ) (q : SignLaw) : Measurable (callMean L q) := by
  have hm (S : Bool) : Measurable (fun d => conditionalMean levelMeasure
      (gapParameter S d) (cutoffProcedure L)) :=
    (measurable_seeded_integral levelMeasure _ (cutoffProcedure L).measurable_output).comp
      (measurable_gapParameter S)
  exact (q.property.1.mul (hm true)).add ((measurable_const.sub q.property.1).mul (hm false))

theorem callMean_bounds (L : ℕ) (q : SignLaw) (d : Gap) :
    0 ≤ callMean L q d ∧ callMean L q d ≤ 1 := by
  obtain ⟨h₀,h₁⟩ := cutoff_conditional_mean_bounds L (gapParameter false d)
  obtain ⟨h₂,h₃⟩ := cutoff_conditional_mean_bounds L (gapParameter true d)
  have hq₀ := (q.property.2 d).1
  have hq₁ := (q.property.2 d).2
  unfold callMean
  constructor
  · exact add_nonneg (mul_nonneg hq₀ h₂) (mul_nonneg (sub_nonneg.mpr hq₁) h₀)
  · calc
      _ ≤ q.val d * 1 + (1-q.val d)*1 :=
        add_le_add (mul_le_mul_of_nonneg_left h₃ hq₀)
          (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hq₁))
      _ = 1 := by ring

theorem callMean_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    Integrable (callMean L q) μ := by
  apply Integrable.of_bound (measurable_callMean L q).aestronglyMeasurable 1
  exact ae_of_all _ (fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg (callMean_bounds L q d).1]
    exact (callMean_bounds L q d).2)

theorem callMean_bias (L : ℕ) (q : SignLaw) (d : Gap) :
    |callMean L q d-q.val d| ≤ callBiasScale L d := by
  have h₁ : |conditionalMean levelMeasure (gapParameter true d) (cutoffProcedure L)-1| ≤
      callBiasScale L d := cutoff_bias_le L d true d.property.1 d.property.2
  have h₀ : |conditionalMean levelMeasure (gapParameter false d) (cutoffProcedure L)-0| ≤
      callBiasScale L d := cutoff_bias_le L d false d.property.1 d.property.2
  have hq₀ := (q.property.2 d).1
  have hq₁ := sub_nonneg.mpr (q.property.2 d).2
  have he : callMean L q d-q.val d =
      q.val d*(conditionalMean levelMeasure (gapParameter true d) (cutoffProcedure L)-1) +
      (1-q.val d)*(conditionalMean levelMeasure (gapParameter false d) (cutoffProcedure L)-0) := by
    unfold callMean; ring
  rw [he]
  calc
    _ ≤ |q.val d*(conditionalMean levelMeasure (gapParameter true d) (cutoffProcedure L)-1)| +
        |(1-q.val d)*(conditionalMean levelMeasure (gapParameter false d) (cutoffProcedure L)-0)| :=
      abs_add_le _ _
    _ ≤ q.val d*callBiasScale L d + (1-q.val d)*callBiasScale L d := by
      rw [abs_mul,abs_mul,abs_of_nonneg hq₀,abs_of_nonneg hq₁]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ hq₀) (mul_le_mul_of_nonneg_left h₀ hq₁)
    _ = _ := by ring

theorem cutoff_population_bias_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    |populationMean μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
        (cutoffProcedure L)-signMean μ q.val| ≤ ∫ d, callBiasScale L d ∂μ := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (cutoff_population_second_le L μ q)
  rw [population_mean_formula μ levelMeasure _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
    (cutoffProcedure L) hfin]
  change |(∫ d, callMean L q d ∂μ)-(∫ d, q.val d ∂μ)| ≤ _
  have hq : Integrable q.val μ := by
    apply Integrable.of_bound q.property.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by
      rw [Real.norm_eq_abs,abs_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2)
  have hi := (callMean_integrable L μ q).sub hq
  rw [← integral_sub (callMean_integrable L μ q) hq]
  exact abs_integral_le_integral_abs.trans
    (integral_mono hi.abs (callBiasScale_integrable L μ) (callMean_bias L q))


end ThresholdHC.BlindUpper
