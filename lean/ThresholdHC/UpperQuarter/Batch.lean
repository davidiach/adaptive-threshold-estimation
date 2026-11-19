import ThresholdHC.UpperQuarter.Moments
import ThresholdHC.UpperDisagreement.Batch

/-! The population and batch bounds with the vote-change bound.

Per coin, the second moment is at most `13/2*callScale + (129/25)*regime`, and
the padded cost at most `11/2*callScale - (9/2)*regime` (`UpperDisagreement`).
Since `(129/25)*(11/2) ≤ (13/2)*(9/2)`, the variance times the padded cost is at
most `(143/4)*A^2`, and the mean-square error at most `147/4` times the
squared modulus. -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

section QuarterBatch
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem cutoff_secondMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (13/2) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ + (129/25) * UpperDisagreement.regimeTerm L d := by
  rw [cutoff_secondMoment_eq]
  exact secondMomentK_le L d S hd hdmax

theorem cutoff_conditional_second_le (L : ℕ) (d : Gap) (S : Bool) :
    conditionalSecondMoment levelMeasure (gapParameter S d) (cutoffProcedure L) ≤
      ENNReal.ofReal ((13/2)*callScale L d + (129/25)*UpperDisagreement.gapRegime L d) := by
  rw [cutoff_conditional_second]
  exact ENNReal.ofReal_le_ofReal (cutoff_secondMoment_le L d S d.property.1 d.property.2)

theorem cutoff_population_second_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    populationSecondMoment μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
      (cutoffProcedure L) ≤
      ENNReal.ofReal ((13/2)*∫ d, callScale L d ∂μ + (129/25)*∫ d, UpperDisagreement.gapRegime L d ∂μ) := by
  rw [population_second_moment_formula μ levelMeasure _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
  have hint : Integrable (fun d => (13/2)*callScale L d + (129/25)*UpperDisagreement.gapRegime L d) μ :=
    ((callScale_integrable L μ).const_mul (13/2)).add ((UpperDisagreement.gapRegime_integrable L μ).const_mul (129/25))
  have hnn : ∀ d, 0 ≤ (13/2)*callScale L d + (129/25)*UpperDisagreement.gapRegime L d := fun d =>
    add_nonneg (mul_nonneg (by norm_num) (callScale_bounds L d).1)
      (mul_nonneg (by norm_num) (UpperDisagreement.gapRegime_bounds L d).1)
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal ((13/2)*callScale L d + (129/25)*UpperDisagreement.gapRegime L d) ∂μ :=
      lintegral_mono (fun d => unit_mixture_bound (signUnit q d) _
        (cutoff_conditional_second_le L d true) (cutoff_conditional_second_le L d false))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn),
        integral_add ((callScale_integrable L μ).const_mul (13/2))
          ((UpperDisagreement.gapRegime_integrable L μ).const_mul (129/25)), integral_const_mul, integral_const_mul]

theorem cutoff_call_second_real_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (cutoffValue L z)^2 ∂callMeasure μ q) ≤
      (13/2)*∫ d, callScale L d ∂μ + (129/25)*∫ d, UpperDisagreement.gapRegime L d ∂μ := by
  have hb : (∫⁻ z, ENNReal.ofReal ((cutoffValue L z)^2) ∂callMeasure μ q) ≤
      ENNReal.ofReal ((13/2)*∫ d, callScale L d ∂μ + (129/25)*∫ d, UpperDisagreement.gapRegime L d ∂μ) := by
    have he := (populationInput_preserving μ levelMeasure (gapParameter false) (gapParameter true)
      (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q)).lintegral_comp
        (ENNReal.measurable_ofReal.comp ((measurable_cutoffValue L).pow_const 2))
    exact he ▸ cutoff_population_second_le L μ q
  rw [← ofReal_integral_eq_lintegral_ofReal (cutoff_call_sq_integrable L μ q)
    (ae_of_all _ (fun z => sq_nonneg _))] at hb
  have h0 : 0 ≤ (13/2)*∫ d, callScale L d ∂μ + (129/25)*∫ d, UpperDisagreement.gapRegime L d ∂μ :=
    add_nonneg (mul_nonneg (by norm_num) (integral_nonneg (fun d => (callScale_bounds L d).1)))
      (mul_nonneg (by norm_num) (integral_nonneg (fun d => (UpperDisagreement.gapRegime_bounds L d).1)))
  exact (ENNReal.ofReal_le_ofReal_iff h0).mp hb

/-- Mean-square error of the calibrated batch at level `L`. -/
theorem cutoffBatch_mse (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂calibrationLaw (callMeasure μ q)) ≤
      ENNReal.ofReal ((147/4)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) := by
  let ν := callMeasure μ q
  let A : ℝ := ∫ d, callScale L d ∂μ
  let Bt : ℝ := ∫ d, UpperDisagreement.gapRegime L d ∂μ
  let w : ℝ := modulus μ (1/Real.sqrt ((2 : ℝ)^L))
  let c : ℝ := ∫ z, paddedRealCost L z ∂ν
  let v : ℝ := variance (cutoffValue L) ν
  let b : ℝ := (∫ z, cutoffValue L z ∂ν)-signMean μ q.val
  have hZ : MemLp (cutoffValue L) 2 ν :=
    (memLp_two_iff_integrable_sq (measurable_cutoffValue L).aestronglyMeasurable).mpr
      (cutoff_call_sq_integrable L μ q)
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q)
  have he : (∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-signMean μ q.val)^2) ∂calibrationLaw ν) =
      ENNReal.ofReal (v*c/(2 : ℝ)^L+b^2) :=
    calibration_cost_mse ν ((2 : ℝ)^L) (by positivity) (paddedRealCost L) (paddedRealCost_bounds L)
      (measurable_paddedRealCost L) hc (cutoffValue L) (measurable_cutoffValue L) hZ (signMean μ q.val)
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have hv : v ≤ (13/2)*A + (129/25)*Bt :=
    (variance_le_expectation_sq (measurable_cutoffValue L).aestronglyMeasurable).trans
      (cutoff_call_second_real_le L μ q)
  have hcu : c ≤ (11/2)*A - (9/2)*Bt := UpperDisagreement.paddedCutoff_work_upper L μ q
  have hA₀ : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (callScale_integral_one_le L μ)
  have hB₀ : 0 ≤ Bt := integral_nonneg (fun d => (UpperDisagreement.gapRegime_bounds L d).1)
  have hv₀ : 0 ≤ v := variance_nonneg _ _
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hb : |b| ≤ w := (cutoff_call_bias_le L μ q).trans (callBiasScale_integral_le_modulus L μ)
  have hb₂ : b^2 ≤ w^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hw).mpr hb
  have hvc : v*c ≤ (143/4)*A^2 := by
    have h1 : v*c ≤ ((13/2)*A + (129/25)*Bt)*((11/2)*A - (9/2)*Bt) :=
      mul_le_mul hv hcu hc.le (by positivity)
    nlinarith [mul_nonneg hA₀ hB₀, sq_nonneg Bt]
  have hprod : v*c/(2 : ℝ)^L ≤ (143/4)*A^2/(2 : ℝ)^L :=
    div_le_div_of_nonneg_right hvc (by positivity)
  have hA : A = Real.sqrt ((2 : ℝ)^L)*w := callScale_integral_eq_modulus L μ
  have hscale : (143/4)*A^2/(2 : ℝ)^L = (143/4)*w^2 := by
    rw [hA]
    calc
      _ = (143/4)*(Real.sqrt ((2 : ℝ)^L))^2*w^2/(2 : ℝ)^L := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]; field_simp
  rw [hscale] at hprod
  change v*c/(2 : ℝ)^L+b^2 ≤ (147/4)*w^2
  linarith


end QuarterBatch

end ThresholdHC.UpperQuarter
