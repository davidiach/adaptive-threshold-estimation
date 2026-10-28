import ThresholdHC.CriticalUpper.ScreenPopulation

/-! Bias and second-moment identities in the actual population experiment. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem screenValue_mem (A₀ A₁ : ℝ) (L : ℕ) (ω : ℕ → Bool) :
    screenValue A₀ A₁ L ω ∈ Icc (0 : ℝ) 1 := by
  rcases screenDecision_zero_or_one A₀ A₁ (fun k => dyadicMean Tier2.observations k ω) L with h | h
  all_goals change screenValue A₀ A₁ L ω = _ at h
  all_goals simp [h]

theorem screen_value_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → (ℕ → Bool)) (hT : Measurable T)
    (A₀ A₁ : ℝ) (L : ℕ) : Integrable (fun z => screenValue A₀ A₁ L (T z)) μ := by
  apply Integrable.of_bound ((measurable_screenValue A₀ A₁ L).comp hT).aestronglyMeasurable 1
  exact ae_of_all _ (fun z => by
    change ‖screenValue A₀ A₁ L (T z)‖ ≤ 1
    rw [Real.norm_of_nonneg (screenValue_mem A₀ A₁ L (T z)).1]
    exact (screenValue_mem A₀ A₁ L (T z)).2)

theorem screen_conditional_mean (A₀ A₁ : ℝ) (L : ℕ) (p : unitInterval) :
    conditionalMean (Measure.dirac ()) p (screenProcedure A₀ A₁ L) =
      ∫ ω, screenValue A₀ A₁ L ω ∂Tier2.tapeMeasure p := by
  change (∫ z : Unit × (ℕ → Bool), screenValue A₀ A₁ L z.2
    ∂(Measure.dirac ()).prod (Tier2.tapeMeasure p)) = _
  rw [integral_prod _ (screen_value_integrable _ Prod.snd measurable_snd A₀ A₁ L)]
  simp

theorem screen_conditional_bias (A₀ A₁ : ℝ) (L : ℕ) (b : Bool) (d : ℝ) :
    |conditionalMean (Measure.dirac ()) (criticalParameter d b) (screenProcedure A₀ A₁ L)-Tier2.bit b| ≤
      screenConditionalError A₀ A₁ L b d := by
  rw [screen_conditional_mean,screenConditionalError_integral]
  have hi := screen_value_integrable (Tier2.tapeMeasure (criticalParameter d b)) id measurable_id A₀ A₁ L
  change Integrable (screenValue A₀ A₁ L) (Tier2.tapeMeasure (criticalParameter d b)) at hi
  calc
    _ = |∫ ω, screenValue A₀ A₁ L ω-Tier2.bit b ∂Tier2.tapeMeasure (criticalParameter d b)| := by
      rw [integral_sub hi (integrable_const (Tier2.bit b))]; simp
    _ ≤ _ := abs_integral_le_integral_abs

theorem screen_conditional_mean_bounds (A₀ A₁ : ℝ) (L : ℕ) (p : unitInterval) :
    conditionalMean (Measure.dirac ()) p (screenProcedure A₀ A₁ L) ∈ Icc (0 : ℝ) 1 := by
  rw [screen_conditional_mean]
  refine ⟨integral_nonneg (fun ω => (screenValue_mem A₀ A₁ L ω).1),?_⟩
  have h := integral_mono (screen_value_integrable (Tier2.tapeMeasure p) id measurable_id A₀ A₁ L)
    (integrable_const (1 : ℝ)) (fun ω => (screenValue_mem A₀ A₁ L ω).2)
  simpa using h

theorem integrable_prior_screen_mean (A₀ A₁ : ℝ) (L : ℕ) (b : Bool)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    Integrable (fun d => (q d : ℝ)*
      conditionalMean (Measure.dirac ()) (criticalParameter d b) (screenProcedure A₀ A₁ L)) criticalGapLaw := by
  have hm := (measurable_conditionalMean (Measure.dirac ()) (screenProcedure A₀ A₁ L)).comp
    (measurable_criticalParameter b)
  apply Integrable.of_bound ((measurable_subtype_coe.comp hq).mul hm).aestronglyMeasurable 1
  refine ae_of_all _ (fun d => ?_)
  have hb := screen_conditional_mean_bounds A₀ A₁ L (criticalParameter d b)
  change ‖(q d : ℝ)*conditionalMean (Measure.dirac ()) (criticalParameter d b) (screenProcedure A₀ A₁ L)‖ ≤ 1
  rw [Real.norm_of_nonneg (mul_nonneg (q d).property.1 hb.1)]
  exact (mul_le_mul_of_nonneg_left hb.2 (q d).property.1).trans (by simpa using (q d).property.2)

theorem screen_population_mean_formula (A₀ A₁ : ℝ) (L : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    populationMean criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (screenProcedure A₀ A₁ L) =
    ∫ d, (q d : ℝ)*conditionalMean (Measure.dirac ()) (criticalParameter d true) (screenProcedure A₀ A₁ L)+
      (1-(q d : ℝ))*conditionalMean (Measure.dirac ()) (criticalParameter d false) (screenProcedure A₀ A₁ L)
        ∂criticalGapLaw := by
  apply population_integral _ _ _ _ _ _ (screenProcedure A₀ A₁ L).measurable_output
  exact screen_value_integrable _ _
    ((measurable_populationInput _ _ q (measurable_criticalParameter false)
      (measurable_criticalParameter true) hq).snd) A₀ A₁ L

theorem screen_population_bias_le (A₀ A₁ : ℝ) (L : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    |populationMean criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (screenProcedure A₀ A₁ L)
      -(∫ d, (q d : ℝ) ∂criticalGapLaw)| ≤ screenPopulationError A₀ A₁ L q := by
  let m (b : Bool) (d : ℝ) := conditionalMean (Measure.dirac ()) (criticalParameter d b) (screenProcedure A₀ A₁ L)
  have hn : Integrable (fun d => (1-(q d : ℝ))*m false d) criticalGapLaw := by
    simpa only [unitInterval.coe_symm_eq] using
      integrable_prior_screen_mean A₀ A₁ L false (fun d => unitInterval.symm (q d))
        (unitInterval.continuous_symm.measurable.comp hq)
  have hm := (integrable_prior_screen_mean A₀ A₁ L true q hq).add hn
  have hdiff := hm.sub (integrable_unitPrior q hq)
  have he : Integrable (fun d => (1-(q d : ℝ))*screenConditionalError A₀ A₁ L false d) criticalGapLaw := by
    simpa only [unitInterval.coe_symm_eq] using
      integrable_prior_screen_error A₀ A₁ L false (fun d => unitInterval.symm (q d))
        (unitInterval.continuous_symm.measurable.comp hq)
  have hsplit := integral_sub hm (integrable_unitPrior q hq)
  simp only [Pi.add_apply,Pi.sub_apply,m] at hsplit
  rw [screen_population_mean_formula A₀ A₁ L q hq,← hsplit]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono hdiff.abs ((integrable_prior_screen_error A₀ A₁ L true q hq).add he)
  intro d
  have hp := abs_le.mp (screen_conditional_bias A₀ A₁ L true d)
  have hn := abs_le.mp (screen_conditional_bias A₀ A₁ L false d)
  simp only [Tier2.bit,ite_true,Bool.false_eq_true,ite_false,sub_zero] at hp hn
  apply abs_le.mpr
  have hp0 := mul_le_mul_of_nonneg_left hp.1 (q d).property.1
  have hp1 := mul_le_mul_of_nonneg_left hp.2 (q d).property.1
  have hn0 := mul_le_mul_of_nonneg_left hn.1 (sub_nonneg.mpr (q d).property.2)
  have hn1 := mul_le_mul_of_nonneg_left hn.2 (sub_nonneg.mpr (q d).property.2)
  dsimp only [m,Pi.add_apply,Pi.sub_apply]
  constructor <;> nlinarith only [hp0,hp1,hn0,hn1]

theorem screen_population_second_moment (A₀ A₁ : ℝ) (L : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    populationSecondMoment criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (screenProcedure A₀ A₁ L) =
    ENNReal.ofReal (populationMean criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (screenProcedure A₀ A₁ L)) := by
  let T := fun z : ℝ × (ℝ × (Unit × (ℕ → ℝ))) =>
    (populationInput (fun d => criticalParameter d false) (fun d => criticalParameter d true) q z).2
  have hT : Measurable T := (measurable_populationInput _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq).snd
  let : IsProbabilityMeasure (populationMeasure criticalGapLaw (Measure.dirac ())) := by
    unfold populationMeasure
    infer_instance
  have hi := screen_value_integrable (populationMeasure criticalGapLaw (Measure.dirac ())) T hT A₀ A₁ L
  have he (z) : (screenValue A₀ A₁ L (T z))^2 = screenValue A₀ A₁ L (T z) := by
    rcases screenDecision_zero_or_one A₀ A₁ (fun k => dyadicMean Tier2.observations k (T z)) L with h | h
    all_goals change screenValue A₀ A₁ L (T z) = _ at h
    all_goals simp [h]
  change (∫⁻ z, ENNReal.ofReal ((screenValue A₀ A₁ L (T z))^2)
    ∂populationMeasure criticalGapLaw (Measure.dirac ())) =
      ENNReal.ofReal (∫ z, screenValue A₀ A₁ L (T z) ∂populationMeasure criticalGapLaw (Measure.dirac ()))
  simp_rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun z => (screenValue_mem A₀ A₁ L (T z)).1))).symm

theorem screen_population_second_moment_le (A₀ A₁ : ℝ) (L : ℕ) (ρ : ℝ)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    populationSecondMoment criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (screenProcedure A₀ A₁ L) ≤
    ENNReal.ofReal (ρ+screenPopulationError A₀ A₁ L q) := by
  rw [screen_population_second_moment A₀ A₁ L q hq]
  apply ENNReal.ofReal_le_ofReal
  have hb := (abs_le.mp (screen_population_bias_le A₀ A₁ L q hq)).2
  linarith

end ThresholdHC.CriticalUpper
