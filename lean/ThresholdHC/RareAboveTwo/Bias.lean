import ThresholdHC.RareAboveTwo.CoupledModel

/-! The calibrated classifier converges to the population sign mean. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.ObservableSimulation

theorem calibratedValue_integrable (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (a ρ : ℝ) (j : ℕ) : Integrable (calibratedValue a ρ j) μ :=
  integrable_binary (measurable_calibratedValue a ρ j) (calibratedValue_binary a ρ j)

theorem calibratedValue_bounds (a ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) :
    calibratedValue a ρ j ω ∈ Icc (0 : ℝ) 1 := by
  rcases calibratedValue_binary a ρ j ω with h | h <;> simp [h]

def conditionalValueMean (a ρ : ℝ) (j : ℕ) (b : Bool) (d : Gap) : ℝ :=
  ∫ ω, calibratedValue a ρ j ω ∂Tier2.tapeMeasure (gapParameter b d)

theorem conditionalValueMean_bounds (a ρ : ℝ) (j : ℕ) (b : Bool) (d : Gap) :
    conditionalValueMean a ρ j b d ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun ω => (calibratedValue_bounds a ρ j ω).1),?_⟩
  have h := integral_mono (calibratedValue_integrable (Tier2.tapeMeasure (gapParameter b d)) a ρ j)
    (integrable_const (1 : ℝ)) (fun ω => (calibratedValue_bounds a ρ j ω).2)
  simpa [conditionalValueMean] using h

theorem measurable_conditionalValueMean (a ρ : ℝ) (j : ℕ) (b : Bool) :
    Measurable (conditionalValueMean a ρ j b) :=
  (CriticalUpper.measurable_tape_integral _ (measurable_calibratedValue a ρ j)).comp (measurable_gapParameter b)

theorem conditionalValueMean_bias (a ρ : ℝ) (j : ℕ) (b : Bool) (d : Gap) :
    |conditionalValueMean a ρ j b d-Tier2.bit b| ≤ calibratedError a ρ j b d := by
  calc
    _ = |∫ ω, calibratedValue a ρ j ω-Tier2.bit b ∂Tier2.tapeMeasure (gapParameter b d)| := by
      rw [integral_sub (calibratedValue_integrable _ a ρ j) (integrable_const _)]; simp [conditionalValueMean]
    _ ≤ _ := abs_integral_le_integral_abs

theorem calibratedValue_bias_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (a ρ : ℝ) (j : ℕ) :
    |(∫ ω, calibratedValue a ρ j ω ∂originalPopulationTapeLaw μ q)-signMean μ q.val| ≤ populationError μ q a ρ j := by
  let m := conditionalValueMean a ρ j
  have hm : Integrable (fun d => q.val d*m true d+(1-q.val d)*m false d) μ := by
    apply Integrable.of_bound ((q.property.1.mul (measurable_conditionalValueMean a ρ j true)).add
      ((measurable_const.sub q.property.1).mul (measurable_conditionalValueMean a ρ j false))).aestronglyMeasurable 1
    refine ae_of_all _ (fun d => ?_)
    have hp := conditionalValueMean_bounds a ρ j true d
    have hn := conditionalValueMean_bounds a ρ j false d
    have hq := q.property.2 d
    change ‖q.val d*m true d+(1-q.val d)*m false d‖ ≤ 1
    have h₀ : 0 ≤ q.val d*m true d+(1-q.val d)*m false d :=
      add_nonneg (mul_nonneg hq.1 hp.1) (mul_nonneg (sub_nonneg.mpr hq.2) hn.1)
    rw [Real.norm_of_nonneg h₀]
    have h₁ := mul_le_mul_of_nonneg_left hp.2 hq.1
    have h₂ := mul_le_mul_of_nonneg_left hn.2 (sub_nonneg.mpr hq.2)
    change _ ≤ q.val d*1 at h₁
    change _ ≤ (1-q.val d)*1 at h₂
    dsimp [m]
    nlinarith only [h₁,h₂]
  have hqi : Integrable q.val μ := by
    apply Integrable.of_bound q.property.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2)
  have he := integral_sub hm hqi
  rw [originalTape_integral_mixture μ q _ (measurable_calibratedValue a ρ j) 1
    (fun ω => by rw [abs_of_nonneg (calibratedValue_bounds a ρ j ω).1]; exact (calibratedValue_bounds a ρ j ω).2)]
  change |(∫ d, q.val d*m true d+(1-q.val d)*m false d ∂μ)-(∫ d, q.val d ∂μ)| ≤ _
  rw [← he]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hm.sub hqi).abs (populationError_integrable μ q a ρ j)
  intro d
  have hp := abs_le.mp (conditionalValueMean_bias a ρ j true d)
  have hn := abs_le.mp (conditionalValueMean_bias a ρ j false d)
  simp only [Tier2.bit,ite_true,Bool.false_eq_true,ite_false,sub_zero] at hp hn
  have hp0 := mul_le_mul_of_nonneg_left hp.1 (q.property.2 d).1
  have hp1 := mul_le_mul_of_nonneg_left hp.2 (q.property.2 d).1
  have hn0 := mul_le_mul_of_nonneg_left hn.1 (sub_nonneg.mpr (q.property.2 d).2)
  have hn1 := mul_le_mul_of_nonneg_left hn.2 (sub_nonneg.mpr (q.property.2 d).2)
  dsimp only [m,Pi.add_apply,Pi.sub_apply]
  apply abs_le.mpr
  constructor <;> nlinarith only [hp0,hp1,hn0,hn1]

theorem calibratedValue_bias (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) (j : ℕ) :
    |(∫ ω, calibratedValue a ρ j ω ∂originalPopulationTapeLaw μ q)-signMean μ q.val| ≤
      3*ρ*CriticalUpper.screenAccuracy j :=
  (calibratedValue_bias_le μ q a ρ j).trans (populationError_bound μ α a ρ hα ha ha' hρ hρ1 hm q hq j)

end ThresholdHC.RareAboveTwo
