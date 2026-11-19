import ThresholdHC.UpperScale.Seed
import ThresholdHC.UpperCallCost.Batch

/-! The mean-square error of the calibrated batch at the scale `t*2^L`.

At calibration scale `N`, the mean-square error of the calibrated batch is
`v*c/N + b^2`, with `v` the variance of one call, `c` its mean padded cost and
`b` its bias (`BlindUpper.calibration_cost_mse`). With the second moment
`13/2*A + (129/25)*B` of `UpperQuarter` and the padded cost
`26/5*A - (21/5)*B` of `UpperCallCost`, where `A` is the average call scale and
`B` the average regime term, `v*c ≤ (169/5)*A^2`. Since `A^2 = 2^L*ω^2` and
`b^2 ≤ ω^2`, with `ω = ω(2^{-L/2})`, the mean-square error at scale `t*2^L`,
`t ≥ 1`, is at most `(1 + (169/5)/t)*ω^2`. -/
noncomputable section
namespace ThresholdHC.UpperScale
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

/-- The variance of one call times its mean padded cost. -/
theorem call_variance_cost_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    variance (cutoffValue L) (callMeasure μ q) * (∫ z, paddedRealCost L z ∂callMeasure μ q) ≤
      (169/5) * (∫ d, callScale L d ∂μ) ^ 2 := by
  set A : ℝ := ∫ d, callScale L d ∂μ
  set Bt : ℝ := ∫ d, UpperDisagreement.gapRegime L d ∂μ
  set c : ℝ := ∫ z, paddedRealCost L z ∂callMeasure μ q
  set v : ℝ := variance (cutoffValue L) (callMeasure μ q)
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q)
  have hv : v ≤ (13/2)*A + (129/25)*Bt :=
    (variance_le_expectation_sq (measurable_cutoffValue L).aestronglyMeasurable).trans
      (UpperQuarter.cutoff_call_second_real_le L μ q)
  have hcu : c ≤ (26/5)*A - (21/5)*Bt := UpperCallCost.paddedCutoff_work_upper L μ q
  have hA₀ : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (callScale_integral_one_le L μ)
  have hB₀ : 0 ≤ Bt := integral_nonneg (fun d => (UpperDisagreement.gapRegime_bounds L d).1)
  have hv₀ : 0 ≤ v := variance_nonneg _ _
  have h1 : v*c ≤ ((13/2)*A + (129/25)*Bt)*((26/5)*A - (21/5)*Bt) :=
    mul_le_mul hv hcu hc.le (by positivity)
  nlinarith [mul_nonneg hA₀ hB₀, sq_nonneg Bt]

/-- Mean-square error of the calibrated batch at the scale `t*2^L`. -/
theorem scaledBatch_mse (L : ℕ) {t : ℝ} (ht : 1 ≤ t) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) :
    (∫⁻ z, ENNReal.ofReal ((scaledBatchOutput L t z - signMean μ q.val) ^ 2)
      ∂calibrationLaw (callMeasure μ q)) ≤
      ENNReal.ofReal ((1 + (169/5) / t) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) := by
  let ν := callMeasure μ q
  let A : ℝ := ∫ d, callScale L d ∂μ
  let w : ℝ := modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))
  let c : ℝ := ∫ z, paddedRealCost L z ∂ν
  let v : ℝ := variance (cutoffValue L) ν
  let b : ℝ := (∫ z, cutoffValue L z ∂ν) - signMean μ q.val
  have hZ : MemLp (cutoffValue L) 2 ν :=
    (memLp_two_iff_integrable_sq (measurable_cutoffValue L).aestronglyMeasurable).mpr
      (cutoff_call_sq_integrable L μ q)
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q)
  have he : (∫⁻ z, ENNReal.ofReal ((scaledBatchOutput L t z - signMean μ q.val) ^ 2)
      ∂calibrationLaw ν) = ENNReal.ofReal (v*c/calScale L t + b^2) :=
    calibration_cost_mse ν (calScale L t) (calScale_pos L t) (paddedRealCost L)
      (paddedRealCost_scale_bounds L t) (measurable_paddedRealCost L) hc (cutoffValue L)
      (measurable_cutoffValue L) hZ (signMean μ q.val)
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hb : |b| ≤ w := (cutoff_call_bias_le L μ q).trans (callBiasScale_integral_le_modulus L μ)
  have hb₂ : b^2 ≤ w^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hw).mpr hb
  have hvc : v*c ≤ (169/5)*A^2 := call_variance_cost_le L μ q
  have hA : A = Real.sqrt ((2 : ℝ)^L)*w := callScale_integral_eq_modulus L μ
  have hA2 : A^2 = (2 : ℝ)^L * w^2 := by
    rw [hA, mul_pow, Real.sq_sqrt (by positivity)]
  have hN : calScale L t = t * (2 : ℝ)^L := by rw [calScale, scaleRatio_of_one_le ht]
  have ht0 : 0 < t := by linarith
  have h2 : (0 : ℝ) < (2 : ℝ)^L := by positivity
  have hprod : v*c/calScale L t ≤ (169/5) / t * w^2 := by
    rw [hN, div_le_iff₀ (mul_pos ht0 h2)]
    calc
      v*c ≤ (169/5)*A^2 := hvc
      _ = (169/5) / t * w^2 * (t * (2 : ℝ)^L) := by
        rw [hA2]
        field_simp
  change v*c/calScale L t + b^2 ≤ (1 + (169/5) / t) * w^2
  nlinarith

theorem scaled_squaredRisk_le (L : ℕ) {t : ℝ} (ht : 1 ≤ t) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) :
    squaredRisk (experimentLaw μ (scaledEstimator L t) q) (populationOutput (scaledEstimator L t))
        (signMean μ q.val) ≤
      ENNReal.ofReal ((1 + (169/5) / t) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) := by
  rw [scaled_squaredRisk_eq]
  exact scaledBatch_mse L ht μ q

end ThresholdHC.UpperScale
