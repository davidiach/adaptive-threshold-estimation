import ThresholdHC.UpperDisagreement.Moments
import ThresholdHC.UpperCost.Batch

/-! The population and batch bounds with the sharper call second moment.

Per coin, the second moment is at most `57/5*callScale + (13/50)*regime` and the
padded cost at most `11/2*callScale - (9/2)*regime` (`Moments`). Averaged over
the gap law, with `A` the average call scale and `B` the average regime term,
the variance times the padded cost is at most
`(57/5*A + 13/50*B)*(11/2*A - 9/2*B) ≤ (627/10)*A^2`, because
`(13/50)*(11/2) ≤ (57/5)*(9/2)`. The mean-square error is then at most
`637/10 = 1 + 627/10` times the squared modulus. -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

/-- The regime term of a gap. -/
def gapRegime (L : ℕ) (d : Gap) : ℝ := regimeTerm L d

theorem gapRegime_bounds (L : ℕ) (d : Gap) :
    0 ≤ gapRegime L d ∧ gapRegime L d ≤ Real.sqrt ((2 : ℝ) ^ L) := by
  refine ⟨regimeTerm_nonneg L d, ?_⟩
  unfold gapRegime regimeTerm
  split_ifs
  · exact le_rfl
  · exact Real.sqrt_nonneg _

theorem measurable_gapRegime (L : ℕ) : Measurable (gapRegime L) := by
  unfold gapRegime regimeTerm
  exact Measurable.ite (measurableSet_le (measurable_const.mul
    (measurable_subtype_coe.pow_const 2)) measurable_const) measurable_const measurable_const

theorem gapRegime_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    Integrable (gapRegime L) μ := by
  apply Integrable.of_bound (measurable_gapRegime L).aestronglyMeasurable (Real.sqrt ((2 : ℝ) ^ L))
  exact ae_of_all _ (fun d => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gapRegime_bounds L d).1]
    exact (gapRegime_bounds L d).2)

theorem cutoff_secondMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (57/5) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ + (13/50) * regimeTerm L d := by
  rw [cutoff_secondMoment_eq]
  exact secondMomentK_le L d S hd hdmax

theorem cutoff_conditional_second_le (L : ℕ) (d : Gap) (S : Bool) :
    conditionalSecondMoment levelMeasure (gapParameter S d) (cutoffProcedure L) ≤
      ENNReal.ofReal ((57/5)*callScale L d + (13/50)*gapRegime L d) := by
  rw [cutoff_conditional_second]
  exact ENNReal.ofReal_le_ofReal (cutoff_secondMoment_le L d S d.property.1 d.property.2)

theorem cutoff_population_second_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    populationSecondMoment μ levelMeasure (gapParameter false) (gapParameter true) (signUnit q)
      (cutoffProcedure L) ≤
      ENNReal.ofReal ((57/5)*∫ d, callScale L d ∂μ + (13/50)*∫ d, gapRegime L d ∂μ) := by
  rw [population_second_moment_formula μ levelMeasure _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
  have hint : Integrable (fun d => (57/5)*callScale L d + (13/50)*gapRegime L d) μ :=
    ((callScale_integrable L μ).const_mul (57/5)).add ((gapRegime_integrable L μ).const_mul (13/50))
  have hnn : ∀ d, 0 ≤ (57/5)*callScale L d + (13/50)*gapRegime L d := fun d =>
    add_nonneg (mul_nonneg (by norm_num) (callScale_bounds L d).1)
      (mul_nonneg (by norm_num) (gapRegime_bounds L d).1)
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal ((57/5)*callScale L d + (13/50)*gapRegime L d) ∂μ :=
      lintegral_mono (fun d => unit_mixture_bound (signUnit q d) _
        (cutoff_conditional_second_le L d true) (cutoff_conditional_second_le L d false))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn),
        integral_add ((callScale_integrable L μ).const_mul (57/5))
          ((gapRegime_integrable L μ).const_mul (13/50)), integral_const_mul, integral_const_mul]

theorem cutoff_call_second_real_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (cutoffValue L z)^2 ∂callMeasure μ q) ≤
      (57/5)*∫ d, callScale L d ∂μ + (13/50)*∫ d, gapRegime L d ∂μ := by
  have hb : (∫⁻ z, ENNReal.ofReal ((cutoffValue L z)^2) ∂callMeasure μ q) ≤
      ENNReal.ofReal ((57/5)*∫ d, callScale L d ∂μ + (13/50)*∫ d, gapRegime L d ∂μ) := by
    have he := (populationInput_preserving μ levelMeasure (gapParameter false) (gapParameter true)
      (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q)).lintegral_comp
        (ENNReal.measurable_ofReal.comp ((measurable_cutoffValue L).pow_const 2))
    exact he ▸ cutoff_population_second_le L μ q
  rw [← ofReal_integral_eq_lintegral_ofReal (cutoff_call_sq_integrable L μ q)
    (ae_of_all _ (fun z => sq_nonneg _))] at hb
  have h0 : 0 ≤ (57/5)*∫ d, callScale L d ∂μ + (13/50)*∫ d, gapRegime L d ∂μ :=
    add_nonneg (mul_nonneg (by norm_num) (integral_nonneg (fun d => (callScale_bounds L d).1)))
      (mul_nonneg (by norm_num) (integral_nonneg (fun d => (gapRegime_bounds L d).1)))
  exact (ENNReal.ofReal_le_ofReal_iff h0).mp hb

theorem cost_bound_nonneg (L : ℕ) (d : Gap) :
    0 ≤ (11/2)*callScale L d - (9/2)*gapRegime L d - rLevel^(L+1) := by
  have h1 := callScale_one_le L d
  have h2 : rLevel^(L+1) ≤ 1 := pow_le_one₀ rLevel_pos.le rLevel_lt_one.le
  unfold gapRegime regimeTerm
  split_ifs with h
  · have hmin : callScale L d = Real.sqrt ((2 : ℝ) ^ L) := by
      unfold callScale
      apply min_eq_left
      rw [← one_div, le_div_iff₀ d.property.1]
      change Real.sqrt (cap L) * (d : ℝ) ≤ 1
      rw [sqrt_cap_mul L d.property.1]
      exact Real.sqrt_le_one.mpr h
    change 0 ≤ (11/2)*callScale L d - (9/2)*Real.sqrt ((2 : ℝ) ^ L) - rLevel^(L+1)
    rw [hmin] at h1 ⊢
    linarith
  · linarith

theorem cutoff_cost_mean_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (11/2) * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ - (9/2) * regimeTerm L d - rLevel ^ (L + 1) := by
  rw [cutoff_cost_mean_eq]
  linarith [paddedWorkMoment_le L d S hd hdmax]

theorem cutoff_conditional_work_le (L : ℕ) (d : Gap) (S : Bool) :
    expectedStoppedProcedureWork levelMeasure (gapParameter S d) (cutoffProcedure L) ≤
      ENNReal.ofReal ((11/2)*callScale L d - (9/2)*gapRegime L d - rLevel^(L+1)) := by
  rw [cutoff_expected_work_real]
  exact ENNReal.ofReal_le_ofReal (cutoff_cost_mean_le L d S d.property.1 d.property.2)

theorem cost_integral (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    ∫ d, ((11/2)*callScale L d - (9/2)*gapRegime L d - rLevel^(L+1)) ∂μ =
      (11/2)*∫ d, callScale L d ∂μ - (9/2)*∫ d, gapRegime L d ∂μ - rLevel^(L+1) := by
  have h1 : Integrable (fun d => (11/2)*callScale L d) μ := (callScale_integrable L μ).const_mul _
  have h2 : Integrable (fun d => (9/2)*gapRegime L d) μ := (gapRegime_integrable L μ).const_mul _
  rw [integral_sub (f := fun d => (11/2)*callScale L d - (9/2)*gapRegime L d) (h1.sub h2)
    (integrable_const _), integral_sub h1 h2, integral_const_mul, integral_const_mul]
  simp

theorem cutoff_call_work_real_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (cutoffCost L z : ℝ) ∂callMeasure μ q) ≤
      (11/2)*∫ d, callScale L d ∂μ - (9/2)*∫ d, gapRegime L d ∂μ - rLevel^(L+1) := by
  have hint : Integrable (fun d => (11/2)*callScale L d - (9/2)*gapRegime L d - rLevel^(L+1)) μ :=
    (((callScale_integrable L μ).const_mul (11/2)).sub
      ((gapRegime_integrable L μ).const_mul (9/2))).sub (integrable_const _)
  have hpop : populationExpectedWork μ levelMeasure (gapParameter false) (gapParameter true)
      (signUnit q) (cutoffProcedure L) ≤
      ENNReal.ofReal ((11/2)*∫ d, callScale L d ∂μ - (9/2)*∫ d, gapRegime L d ∂μ -
        rLevel^(L+1)) := by
    rw [population_work_formula μ levelMeasure _ _ _
      (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
    calc
      _ ≤ ∫⁻ d, ENNReal.ofReal ((11/2)*callScale L d - (9/2)*gapRegime L d - rLevel^(L+1)) ∂μ :=
        lintegral_mono (fun d => unit_mixture_bound (signUnit q d) _
          (cutoff_conditional_work_le L d true) (cutoff_conditional_work_le L d false))
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (cost_bound_nonneg L)),
          cost_integral]
  have hb : (∫⁻ z, stoppedProcedureWork (cutoffProcedure L) z ∂callMeasure μ q) ≤
      ENNReal.ofReal ((11/2)*∫ d, callScale L d ∂μ - (9/2)*∫ d, gapRegime L d ∂μ -
        rLevel^(L+1)) := by
    unfold callMeasure originalPopulationTapeLaw
    rw [← populationInput_work μ levelMeasure (gapParameter false) (gapParameter true)
      (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q) (cutoffProcedure L)]
    exact hpop
  rw [← cutoff_call_work_real] at hb
  have h0 : 0 ≤ (11/2)*∫ d, callScale L d ∂μ - (9/2)*∫ d, gapRegime L d ∂μ - rLevel^(L+1) := by
    rw [← cost_integral]
    exact integral_nonneg (fun d => cost_bound_nonneg L d)
  exact (ENNReal.ofReal_le_ofReal_iff h0).mp hb

theorem paddedCutoff_work_upper (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (paddedCutoffCost L z : ℝ) ∂callMeasure μ q) ≤
      (11/2)*∫ d, callScale L d ∂μ - (9/2)*∫ d, gapRegime L d ∂μ := by
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
    UpperCost.levelTail_integral]
  linarith [cutoff_call_work_real_le L μ q]

/-- Mean-square error of the calibrated batch at level `L`. -/
theorem cutoffBatch_mse (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂calibrationLaw (callMeasure μ q)) ≤
      ENNReal.ofReal ((637/10)*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) := by
  let ν := callMeasure μ q
  let A : ℝ := ∫ d, callScale L d ∂μ
  let Bt : ℝ := ∫ d, gapRegime L d ∂μ
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
  have hv : v ≤ (57/5)*A + (13/50)*Bt :=
    (variance_le_expectation_sq (measurable_cutoffValue L).aestronglyMeasurable).trans
      (cutoff_call_second_real_le L μ q)
  have hcu : c ≤ (11/2)*A - (9/2)*Bt := paddedCutoff_work_upper L μ q
  have hA₀ : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (callScale_integral_one_le L μ)
  have hB₀ : 0 ≤ Bt := integral_nonneg (fun d => (gapRegime_bounds L d).1)
  have hv₀ : 0 ≤ v := variance_nonneg _ _
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hb : |b| ≤ w := (cutoff_call_bias_le L μ q).trans (callBiasScale_integral_le_modulus L μ)
  have hb₂ : b^2 ≤ w^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hw).mpr hb
  have hvc : v*c ≤ (627/10)*A^2 := by
    have h1 : v*c ≤ ((57/5)*A + (13/50)*Bt)*((11/2)*A - (9/2)*Bt) :=
      mul_le_mul hv hcu hc.le (by positivity)
    nlinarith [mul_nonneg hA₀ hB₀, sq_nonneg Bt]
  have hprod : v*c/(2 : ℝ)^L ≤ (627/10)*A^2/(2 : ℝ)^L :=
    div_le_div_of_nonneg_right hvc (by positivity)
  have hA : A = Real.sqrt ((2 : ℝ)^L)*w := callScale_integral_eq_modulus L μ
  have hscale : (627/10)*A^2/(2 : ℝ)^L = (627/10)*w^2 := by
    rw [hA]
    calc
      _ = (627/10)*(Real.sqrt ((2 : ℝ)^L))^2*w^2/(2 : ℝ)^L := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]; field_simp
  rw [hscale] at hprod
  change v*c/(2 : ℝ)^L+b^2 ≤ (637/10)*w^2
  linarith

end ThresholdHC.UpperDisagreement
