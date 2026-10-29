import ThresholdHC.RareAboveTwo.Bias
import ThresholdHC.CriticalUpper.Unbiased

/-! Coupled increments have summable second moments under global rarity. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.Uniform713 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem calibrated_difference_sq_integrable (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (a ρ : ℝ) (j k : ℕ) : Integrable (fun ω => (calibratedValue a ρ j ω-calibratedValue a ρ k ω)^2) μ := by
  apply Integrable.of_bound
    (((measurable_calibratedValue a ρ j).sub (measurable_calibratedValue a ρ k)).pow_const 2).aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by
    change ‖(calibratedValue a ρ j ω-calibratedValue a ρ k ω)^2‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact binary_difference_sq_le_one _ _ (calibratedValue_binary a ρ j ω) (calibratedValue_binary a ρ k ω))

theorem calibrated_difference_coin_moment (a ρ : ℝ) (j k : ℕ) (b : Bool) (d : Gap) :
    (∫ ω, (calibratedValue a ρ j ω-calibratedValue a ρ k ω)^2 ∂Tier2.tapeMeasure (gapParameter b d)) ≤
      calibratedError a ρ j b d+calibratedError a ρ k b d := by
  have hj : Integrable (fun ω => |calibratedValue a ρ j ω-Tier2.bit b|)
      (Tier2.tapeMeasure (gapParameter b d)) := ((integrable_binary (μ := Tier2.tapeMeasure (gapParameter b d))
    (measurable_calibratedValue a ρ j) (calibratedValue_binary a ρ j)).sub (integrable_const (Tier2.bit b))).abs
  have hk : Integrable (fun ω => |calibratedValue a ρ k ω-Tier2.bit b|)
      (Tier2.tapeMeasure (gapParameter b d)) := ((integrable_binary (μ := Tier2.tapeMeasure (gapParameter b d))
    (measurable_calibratedValue a ρ k) (calibratedValue_binary a ρ k)).sub (integrable_const (Tier2.bit b))).abs
  change _ ≤ (∫ ω, |calibratedValue a ρ j ω-Tier2.bit b| ∂Tier2.tapeMeasure (gapParameter b d))+(∫ ω, |calibratedValue a ρ k ω-Tier2.bit b| ∂Tier2.tapeMeasure (gapParameter b d))
  rw [← integral_add hj hk]
  apply integral_mono (calibrated_difference_sq_integrable _ a ρ j k) (hj.add hk)
  intro ω
  exact binary_difference_sq_le _ _ (calibratedValue_binary a ρ j ω) (calibratedValue_binary a ρ k ω) b

theorem calibrated_difference_population_moment (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ : ℝ) (j k : ℕ)
    (q : SignLaw) :
    (∫ ω, (calibratedValue a ρ j ω-calibratedValue a ρ k ω)^2 ∂originalPopulationTapeLaw μ q) ≤
      populationError μ q a ρ j+populationError μ q a ρ k := by
  have hF : Measurable (fun ω => (calibratedValue a ρ j ω-calibratedValue a ρ k ω)^2) :=
    ((measurable_calibratedValue a ρ j).sub (measurable_calibratedValue a ρ k)).pow_const 2
  have hbound (ω) : |(calibratedValue a ρ j ω-calibratedValue a ρ k ω)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact binary_difference_sq_le_one _ _ (calibratedValue_binary a ρ j ω) (calibratedValue_binary a ρ k ω)
  rw [originalTape_integral_mixture μ q _ hF 1 hbound]
  change _ ≤ (∫ d, q.val d*calibratedError a ρ j true d+
    (1-q.val d)*calibratedError a ρ j false d ∂μ)+
    (∫ d, q.val d*calibratedError a ρ k true d+
    (1-q.val d)*calibratedError a ρ k false d ∂μ)
  have hj := populationError_integrable μ q a ρ j
  have hk := populationError_integrable μ q a ρ k
  rw [← integral_add hj hk]
  apply integral_mono_of_nonneg ?_ (hj.add hk) ?_
  · exact ae_of_all _ (fun d => add_nonneg
      (mul_nonneg (q.property.2 d).1 (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (integral_nonneg (fun _ => sq_nonneg _))))
  · refine ae_of_all _ (fun d => ?_)
    have hp := mul_le_mul_of_nonneg_left (calibrated_difference_coin_moment a ρ j k true d) (q.property.2 d).1
    have hn := mul_le_mul_of_nonneg_left (calibrated_difference_coin_moment a ρ j k false d)
      (sub_nonneg.mpr (q.property.2 d).2)
    dsimp only [Pi.add_apply]
    nlinarith only [hp,hn]

theorem calibrated_increment_zero_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    (∫ ω, (increment (fun j => calibratedValue a ρ j ω) 0)^2 ∂originalPopulationTapeLaw μ q) ≤ 2*ρ := by
  have he : (fun ω => (increment (fun j => calibratedValue a ρ j ω) 0)^2) = calibratedValue a ρ 0 := by
    funext ω
    rcases calibratedValue_binary a ρ 0 ω with h | h <;> simp [increment,h]
  rw [he]
  have h := (abs_le.mp (calibratedValue_bias μ α a ρ hα ha ha' hρ hρ1 hm q hq 0)).2
  norm_num [CriticalUpper.screenAccuracy] at h
  change signMean μ q.val ≤ ρ at hq
  linarith

theorem calibrated_increment_succ_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) (j : ℕ) :
    (∫ ω, (increment (fun k => calibratedValue a ρ k ω) (j+1))^2 ∂originalPopulationTapeLaw μ q) ≤
      6*ρ*CriticalUpper.screenAccuracy j := by
  have h := calibrated_difference_population_moment μ a ρ (j+1) j q
  have hp := populationError_bound μ α a ρ hα ha ha' hρ hρ1 hm q hq (j+1)
  have hn := populationError_bound μ α a ρ hα ha ha' hρ hρ1 hm q hq j
  rw [CriticalUpper.screenAccuracy_succ] at hp
  change _ ≤ 6*ρ*CriticalUpper.screenAccuracy j
  have hpos := mul_pos hρ (CriticalUpper.screenAccuracy_pos j)
  exact h.trans (by nlinarith)

end ThresholdHC.RareAboveTwo
