import ThresholdHC.RareAboveTwo.Increment

/-! Exact unbiasedness and a rarity-linear second moment under the actual tape law. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.Uniform713 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal Topology
open Filter

theorem calibrated_increment_integrable_sq (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ : ℝ) (q : SignLaw) (j : ℕ) :
    Integrable (fun ω => (increment (fun k => calibratedValue a ρ k ω) j)^2) (originalPopulationTapeLaw μ q) := by
  cases j with
  | zero =>
    apply Integrable.of_bound ((measurable_calibratedValue a ρ 0).pow_const 2).aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by
      rcases calibratedValue_binary a ρ 0 ω with h | h <;> simp [h])
  | succ j => exact calibrated_difference_sq_integrable _ a ρ (j+1) j

theorem calibrated_normalized_moment_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a)
    (q : SignLaw)
    (hq : RarePrior μ ρ q) (j : ℕ) :
    (∫ ω, (increment (fun k => calibratedValue a ρ k ω) j)^2 ∂originalPopulationTapeLaw μ q)/levelProb j ≤
      24*ρ*(1/8 : ℝ)^j := by
  apply (div_le_iff₀ (levelProb_pos j)).2
  have hl := mul_le_mul_of_nonneg_left (CriticalUpper.levelProb_lower j)
    (show 0 ≤ 24*ρ*(1/8 : ℝ)^j by positivity)
  apply le_trans _ hl
  cases j with
  | zero =>
    have h := calibrated_increment_zero_moment μ α a ρ hα ha ha' hρ hρ1 hm q hq
    norm_num at *
    linarith
  | succ j =>
    have h := calibrated_increment_succ_moment μ α a ρ hα ha ha' hρ hρ1 hm q hq j
    have he : 24*ρ*(1/8 : ℝ)^(j+1)*((1/4 : ℝ)*(1/2 : ℝ)^(j+1)) =
        6*ρ*CriticalUpper.screenAccuracy j := by
      unfold CriticalUpper.screenAccuracy
      calc
        _ = 6*ρ*((1/8 : ℝ)*(1/2 : ℝ))^(j+1) := by rw [mul_pow]; ring
        _ = _ := by
          simp only [show (1/8 : ℝ)*(1/2) = (16 : ℝ)⁻¹ by norm_num,inv_pow]
    exact h.trans_eq he.symm

theorem calibrated_normalized_moments_summable (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a)
    (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    Summable (fun j => (∫ ω, (increment (fun k => calibratedValue a ρ k ω) j)^2
      ∂originalPopulationTapeLaw μ q)/levelProb j) := by
  exact Summable.of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (levelProb_pos j).le)
    (calibrated_normalized_moment_le μ α a ρ hα ha ha' hρ hρ1 hm q hq)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/8) (by norm_num)).mul_left (24*ρ))

theorem rareUnbiased_memLp (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a)
    (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    MemLp (rareUnbiasedProcedure a ρ).output 2 (samplingMeasure (originalPopulationTapeLaw μ q)) := by
  exact estimator_memLp (measurable_calibratedValue a ρ)
    (calibrated_increment_integrable_sq μ a ρ q)
    (calibrated_normalized_moments_summable μ α a ρ hα ha ha' hρ hρ1 hm q hq)

theorem rareUnbiased_second_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a)
    (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    (∫ z, ((rareUnbiasedProcedure a ρ).output z)^2 ∂samplingMeasure (originalPopulationTapeLaw μ q)) ≤ 28*ρ := by
  rw [rareUnbiasedProcedure_output,estimator_second_moment
    (rareUnbiased_memLp μ α a ρ hα ha ha' hρ hρ1 hm q hq)]
  have hs := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/8) (by norm_num)).mul_left (24*ρ)
  calc
    _ ≤ ∑' j, 24*ρ*(1/8 : ℝ)^j :=
      (calibrated_normalized_moments_summable μ α a ρ hα ha ha' hρ hρ1 hm q hq).tsum_le_tsum
        (calibrated_normalized_moment_le μ α a ρ hα ha ha' hρ hρ1 hm q hq) hs.summable
    _ = (24*ρ)*(1-(1/8 : ℝ))⁻¹ := hs.tsum_eq
    _ ≤ _ := by norm_num; linarith

theorem calibratedValue_mean_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a)
    (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    Tendsto (fun j => ∫ ω, calibratedValue a ρ j ω ∂originalPopulationTapeLaw μ q)
      atTop (𝓝 (signMean μ q.val)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _) _
    (show Tendsto (fun j => 3*ρ*CriticalUpper.screenAccuracy j) atTop (𝓝 0) by
      simpa using CriticalUpper.screenAccuracy_tendsto.const_mul (3*ρ))
  intro j
  exact calibratedValue_bias μ α a ρ hα ha ha' hρ hρ1 hm q hq j

theorem rareUnbiased_mean (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a)
    (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    (∫ z, (rareUnbiasedProcedure a ρ).output z ∂samplingMeasure (originalPopulationTapeLaw μ q)) =
      signMean μ q.val := by
  exact estimator_unbiased (fun j => calibratedValue_integrable _ a ρ j)
    ((rareUnbiased_memLp μ α a ρ hα ha ha' hρ hρ1 hm q hq).integrable (by norm_num))
    (calibratedValue_mean_tendsto μ α a ρ hα ha ha' hρ hρ1 hm q hq)

end ThresholdHC.RareAboveTwo
