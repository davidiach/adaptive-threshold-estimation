import ThresholdHC.UpperCost.Moments
import ThresholdHC.UpperMoment.Batch

/-! The population and batch bounds of the distribution-blind estimator with the
sharper padded call cost `11/2` and the call second moment `72/5` of
`UpperMoment`. The padded call takes one flip exactly when its level exceeds
`L`, which has probability `r^{L+1}`; the per-coin bound of `Moments` covers
that flip. The mean-square error is at most `401/5 = 1 + (72/5)*(11/2)` times
the squared modulus. -/
noncomputable section
namespace ThresholdHC.UpperCost
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem cutoff_conditional_work_le (L : ℕ) (d : Gap) (S : Bool) :
    expectedStoppedProcedureWork levelMeasure (gapParameter S d) (cutoffProcedure L) ≤
      ENNReal.ofReal ((11/2)*callScale L d - rLevel^(L+1)) := by
  rw [cutoff_expected_work_real]
  exact ENNReal.ofReal_le_ofReal (cutoff_cost_mean_le L d S d.property.1 d.property.2)

theorem cost_bound_nonneg (L : ℕ) (d : Gap) : 0 ≤ (11/2)*callScale L d - rLevel^(L+1) := by
  have h1 := callScale_one_le L d
  have h2 : rLevel^(L+1) ≤ 1 := pow_le_one₀ rLevel_pos.le rLevel_lt_one.le
  linarith

theorem cutoff_population_work_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    populationExpectedWork μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
      (cutoffProcedure L) ≤
      ENNReal.ofReal ((11/2)*∫ d, callScale L d ∂μ - rLevel^(L+1)) := by
  rw [population_work_formula μ levelMeasure _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
  have hint : Integrable (fun d => (11/2)*callScale L d - rLevel^(L+1)) μ :=
    ((callScale_integrable L μ).const_mul (11/2)).sub (integrable_const _)
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal ((11/2)*callScale L d - rLevel^(L+1)) ∂μ := lintegral_mono (fun d =>
      unit_mixture_bound (signUnit q d) _ (cutoff_conditional_work_le L d true)
        (cutoff_conditional_work_le L d false))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (cost_bound_nonneg L)),
        integral_sub ((callScale_integrable L μ).const_mul (11/2)) (integrable_const _),
        integral_const_mul]
      simp

theorem cutoff_call_work_real_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (cutoffCost L z : ℝ) ∂callMeasure μ q) ≤
      (11/2)*∫ d, callScale L d ∂μ - rLevel^(L+1) := by
  have hb : (∫⁻ z, stoppedProcedureWork (cutoffProcedure L) z ∂callMeasure μ q) ≤
      ENNReal.ofReal ((11/2)*∫ d, callScale L d ∂μ - rLevel^(L+1)) := by
    unfold callMeasure originalPopulationTapeLaw
    rw [← populationInput_work μ levelMeasure (gapParameter false) (gapParameter true)
      (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q) (cutoffProcedure L)]
    exact cutoff_population_work_le L μ q
  rw [← cutoff_call_work_real] at hb
  have h0 : 0 ≤ (11/2)*∫ d, callScale L d ∂μ - rLevel^(L+1) := by
    have h1 := callScale_integral_one_le L μ
    have h2 : rLevel^(L+1) ≤ 1 := pow_le_one₀ rLevel_pos.le rLevel_lt_one.le
    linarith
  exact (ENNReal.ofReal_le_ofReal_iff h0).mp hb

/-- The probability that the level exceeds `L` is `r^{L+1}`. -/
theorem levelTail_integral (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    ∫ z, (if L < z.1 then (1 : ℝ) else 0) ∂callMeasure μ q = rLevel ^ (L + 1) := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hs : HasSum (fun l => levelProb l * (if L < l then (1 : ℝ) else 0)) (rLevel ^ (L + 1)) := by
    rw [← hasSum_nat_add_iff' (L + 1)]
    have h0 : ∑ i ∈ Finset.range (L + 1), levelProb i * (if L < i then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        rw [ite_eq_right (by have := Finset.mem_range.1 hi; omega)]
        ring)
    rw [h0, sub_zero]
    have hg := (hasSum_geometric_of_lt_one hr0.le hr1).mul_left ((1 - rLevel) * rLevel ^ (L + 1))
    convert hg using 1
    · funext n
      rw [ite_eq_left (by omega)]
      unfold levelProb
      ring
    · have hne : 1 - rLevel ≠ 0 := by linarith
      field_simp
  unfold callMeasure
  rw [integral_fun_fst (fun l => if L < l then (1 : ℝ) else 0), integral_levelMeasure, hs.tsum_eq]
  simp

theorem paddedCutoff_work_upper (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (paddedCutoffCost L z : ℝ) ∂callMeasure μ q) ≤ (11/2)*∫ d, callScale L d ∂μ := by
  have hpt : ∀ z : ℕ × (ℕ → Bool), (paddedCutoffCost L z : ℝ) =
      (cutoffCost L z : ℝ) + (if L < z.1 then 1 else 0) := by
    intro z
    unfold paddedCutoffCost cutoffCost
    by_cases h : z.1 ≤ L
    · have hs : 1 ≤ classifierStop z.1 z.2 := Nat.one_le_two_pow
      rw [ite_eq_left h, ite_eq_right (not_lt.2 h), max_eq_right hs]
      simp
    · rw [ite_eq_right h, ite_eq_left (not_le.1 h)]
      simp
  have hm : Measurable (fun z : ℕ × (ℕ → Bool) => if L < z.1 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const measurable_const
  have hi : Integrable (fun z : ℕ × (ℕ → Bool) => if L < z.1 then (1 : ℝ) else 0) (callMeasure μ q) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact ae_of_all _ (fun z => by split_ifs <;> simp)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add (cutoff_call_cost_integrable L μ q) hi,
    levelTail_integral]
  linarith [cutoff_call_work_real_le L μ q]

/-- Mean-square error of the calibrated batch at level `L`. -/
theorem cutoffBatch_mse (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂calibrationLaw (callMeasure μ q)) ≤
      ENNReal.ofReal ((401/5)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) := by
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
  have hv : v ≤ (72/5)*A :=
    (variance_le_expectation_sq (measurable_cutoffValue L).aestronglyMeasurable).trans
      (UpperMoment.cutoff_call_second_real_le L μ q)
  have hcu : c ≤ (11/2)*A := paddedCutoff_work_upper L μ q
  have hA₀ : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (callScale_integral_one_le L μ)
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hb : |b| ≤ w := (cutoff_call_bias_le L μ q).trans (callBiasScale_integral_le_modulus L μ)
  have hb₂ : b^2 ≤ w^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hw).mpr hb
  have hprod : v*c/(2 : ℝ)^L ≤ ((72/5)*A)*((11/2)*A)/(2 : ℝ)^L :=
    div_le_div_of_nonneg_right (mul_le_mul hv hcu hc.le (by positivity)) (by positivity)
  have hA : A = Real.sqrt ((2 : ℝ)^L)*w := callScale_integral_eq_modulus L μ
  have hscale : ((72/5)*A)*((11/2)*A)/(2 : ℝ)^L = (396/5)*w^2 := by
    rw [hA]
    calc
      _ = (396/5)*(Real.sqrt ((2 : ℝ)^L))^2*w^2/(2 : ℝ)^L := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]; field_simp
  rw [hscale] at hprod
  change v*c/(2 : ℝ)^L+b^2 ≤ (401/5)*w^2
  linarith

end ThresholdHC.UpperCost
