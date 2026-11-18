import ThresholdHC.UpperWork.Moments
import ThresholdHC.UpperConstant.Batch

/-! The population and batch bounds of the distribution-blind estimator with the
sharper call cost `248/25` of `Moments` and the call second moment 23 of
`UpperConstant`: the padded cost is at most `273/25`, and the mean-square error
at most `6304/25 = 1 + 23*273/25` times the squared modulus. -/
noncomputable section
namespace ThresholdHC.UpperWork
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem cutoff_conditional_work_le (L : ℕ) (d : Gap) (S : Bool) :
    expectedStoppedProcedureWork levelMeasure (gapParameter S d) (cutoffProcedure L) ≤
      ENNReal.ofReal ((248/25)*callScale L d) := by
  rw [cutoff_expected_work_real]
  exact ENNReal.ofReal_le_ofReal (cutoff_cost_mean_le L d S d.property.1 d.property.2)

theorem cutoff_population_work_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    populationExpectedWork μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
      (cutoffProcedure L) ≤ ENNReal.ofReal ((248/25)*∫ d, callScale L d ∂μ) := by
  rw [population_work_formula μ levelMeasure _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal ((248/25)*callScale L d) ∂μ := lintegral_mono (fun d =>
      unit_mixture_bound (signUnit q d) _ (cutoff_conditional_work_le L d true)
        (cutoff_conditional_work_le L d false))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal ((callScale_integrable L μ).const_mul (248/25))
        (ae_of_all _ (fun d => mul_nonneg (by norm_num) (callScale_bounds L d).1)),integral_const_mul]

theorem cutoff_call_work_real_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (cutoffCost L z : ℝ) ∂callMeasure μ q) ≤ (248/25)*∫ d, callScale L d ∂μ := by
  have hb : (∫⁻ z, stoppedProcedureWork (cutoffProcedure L) z ∂callMeasure μ q) ≤
      ENNReal.ofReal ((248/25)*∫ d, callScale L d ∂μ) := by
    unfold callMeasure originalPopulationTapeLaw
    rw [← populationInput_work μ levelMeasure (gapParameter false) (gapParameter true)
      (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q) (cutoffProcedure L)]
    exact cutoff_population_work_le L μ q
  rw [← cutoff_call_work_real] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
    (integral_nonneg (fun d => (callScale_bounds L d).1)))).mp hb

theorem paddedCutoff_work_upper (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (paddedCutoffCost L z : ℝ) ∂callMeasure μ q) ≤ (273/25)*∫ d, callScale L d ∂μ := by
  have hcost : ∀ z : ℕ × (ℕ → Bool), (paddedCutoffCost L z : ℝ) ≤ (cutoffCost L z : ℝ)+1 := by
    intro z
    have hnat : paddedCutoffCost L z ≤ cutoffCost L z+1 := max_le (by omega) (by omega)
    exact_mod_cast hnat
  have h := integral_mono (paddedCutoff_cost_integrable L μ q)
    ((cutoff_call_cost_integrable L μ q).add (integrable_const 1)) hcost
  change (∫ z, (paddedCutoffCost L z : ℝ) ∂callMeasure μ q) ≤
    (∫ z, (cutoffCost L z : ℝ)+1 ∂callMeasure μ q) at h
  rw [integral_add (cutoff_call_cost_integrable L μ q) (integrable_const 1)] at h
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  have hbase := cutoff_call_work_real_le L μ q
  have hA := callScale_integral_one_le L μ
  linarith

/-- Mean-square error of the calibrated batch at level `L`. -/
theorem cutoffBatch_mse (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂calibrationLaw (callMeasure μ q)) ≤
      ENNReal.ofReal ((6304/25)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) := by
  let ν := callMeasure μ q
  let A : ℝ := ∫ d, callScale L d ∂μ
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
  have hv : v ≤ 23*A := (variance_le_expectation_sq (measurable_cutoffValue L).aestronglyMeasurable).trans
    (UpperConstant.cutoff_call_second_real_le L μ q)
  have hcu : c ≤ (273/25)*A := paddedCutoff_work_upper L μ q
  have hA₀ : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (callScale_integral_one_le L μ)
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hb : |b| ≤ w := (cutoff_call_bias_le L μ q).trans (callBiasScale_integral_le_modulus L μ)
  have hb₂ : b^2 ≤ w^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hw).mpr hb
  have hprod : v*c/(2 : ℝ)^L ≤ (23*A)*((273/25)*A)/(2 : ℝ)^L :=
    div_le_div_of_nonneg_right (mul_le_mul hv hcu hc.le (by positivity)) (by positivity)
  have hA : A = Real.sqrt ((2 : ℝ)^L)*w := callScale_integral_eq_modulus L μ
  have hscale : (23*A)*((273/25)*A)/(2 : ℝ)^L = (6279/25)*w^2 := by
    rw [hA]
    calc
      _ = (6279/25)*(Real.sqrt ((2 : ℝ)^L))^2*w^2/(2 : ℝ)^L := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]; field_simp
  rw [hscale] at hprod
  change v*c/(2 : ℝ)^L+b^2 ≤ (6304/25)*w^2
  linarith

end ThresholdHC.UpperWork
