import ThresholdHC.CriticalUpper.CoinLaw

/-! Coupled increment moments under the full global rarity constraint. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

def calibratedError (ρ : ℝ) (j : ℕ) (b : Bool) : ℝ → ℝ :=
  screenConditionalError (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j) b

def calibratedPopulationError (ρ : ℝ) (j : ℕ) (q : ℝ → unitInterval) : ℝ :=
  screenPopulationError (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j) q

theorem calibratedError_integral (ρ : ℝ) (j : ℕ) (b : Bool) (d : ℝ) :
    calibratedError ρ j b d =
      ∫ ω, |calibratedValue ρ j ω-Tier2.bit b| ∂Tier2.tapeMeasure (criticalParameter d b) :=
  screenConditionalError_integral (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j) b d

theorem calibrated_difference_sq_integrable (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (ρ : ℝ) (j k : ℕ) : Integrable (fun ω => (calibratedValue ρ j ω-calibratedValue ρ k ω)^2) μ := by
  apply Integrable.of_bound
    (((measurable_calibratedValue ρ j).sub (measurable_calibratedValue ρ k)).pow_const 2).aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by
    change ‖(calibratedValue ρ j ω-calibratedValue ρ k ω)^2‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact binary_difference_sq_le_one _ _ (calibratedValue_binary ρ j ω) (calibratedValue_binary ρ k ω))

theorem calibrated_difference_coin_moment (ρ : ℝ) (j k : ℕ) (b : Bool) (d : ℝ) :
    (∫ ω, (calibratedValue ρ j ω-calibratedValue ρ k ω)^2 ∂Tier2.tapeMeasure (criticalParameter d b)) ≤
      calibratedError ρ j b d+calibratedError ρ k b d := by
  have hj : Integrable (fun ω => |calibratedValue ρ j ω-Tier2.bit b|)
      (Tier2.tapeMeasure (criticalParameter d b)) := ((integrable_binary (μ := Tier2.tapeMeasure (criticalParameter d b))
    (measurable_calibratedValue ρ j) (calibratedValue_binary ρ j)).sub (integrable_const (Tier2.bit b))).abs
  have hk : Integrable (fun ω => |calibratedValue ρ k ω-Tier2.bit b|)
      (Tier2.tapeMeasure (criticalParameter d b)) := ((integrable_binary (μ := Tier2.tapeMeasure (criticalParameter d b))
    (measurable_calibratedValue ρ k) (calibratedValue_binary ρ k)).sub (integrable_const (Tier2.bit b))).abs
  rw [calibratedError_integral,calibratedError_integral,← integral_add hj hk]
  apply integral_mono (calibrated_difference_sq_integrable _ ρ j k) (hj.add hk)
  intro ω
  exact binary_difference_sq_le _ _ (calibratedValue_binary ρ j ω) (calibratedValue_binary ρ k ω) b

theorem calibrated_error_mixture_integrable (ρ : ℝ) (j : ℕ) (q : ℝ → unitInterval) (hq : Measurable q) :
    Integrable (fun d => (q d : ℝ)*calibratedError ρ j true d+
      (1-(q d : ℝ))*calibratedError ρ j false d) criticalGapLaw := by
  have hp := integrable_prior_screen_error
    (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j) true q hq
  have hn := integrable_prior_screen_error
    (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j) false
    (fun d => unitInterval.symm (q d)) (unitInterval.continuous_symm.measurable.comp hq)
  convert hp.add hn using 1
  funext d
  simp only [Pi.add_apply,calibratedError,unitInterval.coe_symm_eq]

theorem calibrated_difference_population_moment (ρ : ℝ) (j k : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    (∫ ω, (calibratedValue ρ j ω-calibratedValue ρ k ω)^2 ∂criticalTapeLaw q) ≤
      calibratedPopulationError ρ j q+calibratedPopulationError ρ k q := by
  have hF : Measurable (fun ω => (calibratedValue ρ j ω-calibratedValue ρ k ω)^2) :=
    ((measurable_calibratedValue ρ j).sub (measurable_calibratedValue ρ k)).pow_const 2
  have hbound (ω) : |(calibratedValue ρ j ω-calibratedValue ρ k ω)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact binary_difference_sq_le_one _ _ (calibratedValue_binary ρ j ω) (calibratedValue_binary ρ k ω)
  rw [criticalTapeLaw_integral_mixture q hq _ hF 1 hbound]
  change _ ≤ (∫ d, (q d : ℝ)*calibratedError ρ j true d+
    (1-(q d : ℝ))*calibratedError ρ j false d ∂criticalGapLaw)+
    (∫ d, (q d : ℝ)*calibratedError ρ k true d+
    (1-(q d : ℝ))*calibratedError ρ k false d ∂criticalGapLaw)
  have hj := calibrated_error_mixture_integrable ρ j q hq
  have hk := calibrated_error_mixture_integrable ρ k q hq
  rw [← integral_add hj hk]
  apply integral_mono_of_nonneg ?_ (hj.add hk) ?_
  · exact ae_of_all _ (fun d => add_nonneg
      (mul_nonneg (q d).property.1 (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_nonneg (sub_nonneg.mpr (q d).property.2) (integral_nonneg (fun _ => sq_nonneg _))))
  · refine ae_of_all _ (fun d => ?_)
    have hp := mul_le_mul_of_nonneg_left (calibrated_difference_coin_moment ρ j k true d) (q d).property.1
    have hn := mul_le_mul_of_nonneg_left (calibrated_difference_coin_moment ρ j k false d)
      (sub_nonneg.mpr (q d).property.2)
    dsimp only [Pi.add_apply]
    nlinarith only [hp,hn]

theorem screenAccuracy_succ (j : ℕ) : screenAccuracy (j+1) = screenAccuracy j/16 := by
  unfold screenAccuracy
  rw [pow_succ,mul_inv_rev]
  ring

theorem calibrated_increment_zero_moment (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    (∫ ω, (increment (fun j => calibratedValue ρ j ω) 0)^2 ∂criticalTapeLaw q) ≤ 2*ρ := by
  have he : (fun ω => (increment (fun j => calibratedValue ρ j ω) 0)^2) = calibratedValue ρ 0 := by
    funext ω
    rcases calibratedValue_binary ρ 0 ω with h | h <;> simp [increment,h]
  rw [he]
  have h := (abs_le.mp (calibratedValue_bias ρ hρ hρ1 0 q hq hmass)).2
  norm_num [screenAccuracy] at h
  linarith

theorem calibrated_increment_succ_moment (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    (∫ ω, (increment (fun k => calibratedValue ρ k ω) (j+1))^2 ∂criticalTapeLaw q) ≤
      6*ρ*screenAccuracy j := by
  have h := calibrated_difference_population_moment ρ (j+1) j q hq
  have hp := calibratedScreen_error ρ hρ hρ1 (j+1) q hq hmass
  have hn := calibratedScreen_error ρ hρ hρ1 j q hq hmass
  change calibratedPopulationError ρ (j+1) q ≤ _ at hp
  change calibratedPopulationError ρ j q ≤ _ at hn
  rw [screenAccuracy_succ] at hp
  change _ ≤ 6*ρ*screenAccuracy j
  have hpos := mul_pos hρ (screenAccuracy_pos j)
  exact h.trans (by nlinarith)

end ThresholdHC.CriticalUpper
