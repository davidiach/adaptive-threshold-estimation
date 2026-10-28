import ThresholdHC.CriticalUpper.Increment

/-! Exact unbiasedness and a second-moment bound for the random-level estimator. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

open Filter
open scoped Topology

theorem rLevel_bounds : (1/2 : ℝ) ≤ rLevel ∧ rLevel ≤ (3/4 : ℝ) := by
  have hs : rLevel^2 = (1/2 : ℝ) := by
    unfold rLevel
    rw [inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  constructor <;> nlinarith [rLevel_pos]

theorem levelProb_lower (j : ℕ) : (1/4 : ℝ)*(1/2 : ℝ)^j ≤ levelProb j := by
  unfold levelProb
  exact mul_le_mul (by linarith [rLevel_bounds.2])
    (pow_le_pow_left₀ (by norm_num) rLevel_bounds.1 j)
    (by positivity) (sub_pos.mpr rLevel_lt_one).le

theorem levelProb_upper (j : ℕ) : levelProb j ≤ (3/4 : ℝ)^j := by
  unfold levelProb
  calc
    _ ≤ 1*rLevel^j := mul_le_mul_of_nonneg_right (by linarith [rLevel_pos]) (by positivity [rLevel_pos])
    _ ≤ _ := by simpa only [one_mul] using pow_le_pow_left₀ rLevel_pos.le rLevel_bounds.2 j

theorem calibrated_increment_integrable_sq (ρ : ℝ) (q : ℝ → unitInterval)
    (hq : Measurable q) (j : ℕ) :
    Integrable (fun ω => (increment (fun k => calibratedValue ρ k ω) j)^2) (criticalTapeLaw q) := by
  let := criticalTapeLaw_probability q hq
  cases j with
  | zero =>
    apply Integrable.of_bound ((measurable_calibratedValue ρ 0).pow_const 2).aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by
      rcases calibratedValue_binary ρ 0 ω with h | h <;> simp [h])
  | succ j => exact calibrated_difference_sq_integrable _ ρ (j+1) j

theorem calibrated_normalized_moment_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) (j : ℕ) :
    (∫ ω, (increment (fun k => calibratedValue ρ k ω) j)^2 ∂criticalTapeLaw q)/levelProb j ≤
      24*ρ*(1/8 : ℝ)^j := by
  apply (div_le_iff₀ (levelProb_pos j)).2
  have hl := mul_le_mul_of_nonneg_left (levelProb_lower j)
    (show 0 ≤ 24*ρ*(1/8 : ℝ)^j by positivity)
  apply le_trans _ hl
  cases j with
  | zero =>
    have h := calibrated_increment_zero_moment ρ hρ hρ1 q hq hmass
    norm_num at *
    linarith
  | succ j =>
    have h := calibrated_increment_succ_moment ρ hρ hρ1 j q hq hmass
    have he : 24*ρ*(1/8 : ℝ)^(j+1)*((1/4 : ℝ)*(1/2 : ℝ)^(j+1)) =
        6*ρ*screenAccuracy j := by
      unfold screenAccuracy
      calc
        _ = 6*ρ*((1/8 : ℝ)*(1/2 : ℝ))^(j+1) := by rw [mul_pow]; ring
        _ = _ := by
          simp only [show (1/8 : ℝ)*(1/2) = (16 : ℝ)⁻¹ by norm_num,inv_pow]
    exact h.trans_eq he.symm

theorem calibrated_normalized_moments_summable (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    Summable (fun j => (∫ ω, (increment (fun k => calibratedValue ρ k ω) j)^2
      ∂criticalTapeLaw q)/levelProb j) := by
  exact Summable.of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (levelProb_pos j).le)
    (calibrated_normalized_moment_le ρ hρ hρ1 q hq hmass)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/8) (by norm_num)).mul_left (24*ρ))

theorem criticalUnbiased_memLp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    MemLp (criticalUnbiasedProcedure ρ).output 2 (samplingMeasure (criticalTapeLaw q)) := by
  let := criticalTapeLaw_probability q hq
  exact estimator_memLp (measurable_calibratedValue ρ)
    (calibrated_increment_integrable_sq ρ q hq)
    (calibrated_normalized_moments_summable ρ hρ hρ1 q hq hmass)

theorem criticalUnbiased_second_moment (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    (∫ z, ((criticalUnbiasedProcedure ρ).output z)^2 ∂samplingMeasure (criticalTapeLaw q)) ≤ 28*ρ := by
  let := criticalTapeLaw_probability q hq
  rw [criticalUnbiasedProcedure_output,estimator_second_moment
    (criticalUnbiased_memLp ρ hρ hρ1 q hq hmass)]
  have hs := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/8) (by norm_num)).mul_left (24*ρ)
  calc
    _ ≤ ∑' j, 24*ρ*(1/8 : ℝ)^j :=
      (calibrated_normalized_moments_summable ρ hρ hρ1 q hq hmass).tsum_le_tsum
        (calibrated_normalized_moment_le ρ hρ hρ1 q hq hmass) hs.summable
    _ = (24*ρ)*(1-(1/8 : ℝ))⁻¹ := hs.tsum_eq
    _ ≤ _ := by norm_num; linarith

theorem screenAccuracy_tendsto : Tendsto screenAccuracy atTop (𝓝 0) := by
  have he : screenAccuracy = fun j => (1/16 : ℝ)^j*(1/16 : ℝ) := by
    funext j
    simp only [screenAccuracy,pow_succ,mul_inv_rev]
    rw [← inv_pow]
    ring
  rw [he]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/16) (by norm_num)).mul_const (1/16 : ℝ)

theorem calibratedValue_mean_tendsto (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    Tendsto (fun j => ∫ ω, calibratedValue ρ j ω ∂criticalTapeLaw q)
      atTop (𝓝 (∫ d, (q d : ℝ) ∂criticalGapLaw)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _) _
    (show Tendsto (fun j => 3*ρ*screenAccuracy j) atTop (𝓝 0) by
      simpa using screenAccuracy_tendsto.const_mul (3*ρ))
  intro j
  exact calibratedValue_bias ρ hρ hρ1 j q hq hmass

theorem criticalUnbiased_mean (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    (∫ z, (criticalUnbiasedProcedure ρ).output z ∂samplingMeasure (criticalTapeLaw q)) =
      ∫ d, (q d : ℝ) ∂criticalGapLaw := by
  let := criticalTapeLaw_probability q hq
  exact estimator_unbiased (fun j => calibratedValue_integrable ρ j q hq)
    ((criticalUnbiased_memLp ρ hρ hρ1 q hq hmass).integrable (by norm_num))
    (calibratedValue_mean_tendsto ρ hρ hρ1 q hq hmass)

end ThresholdHC.CriticalUpper
