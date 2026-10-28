import ThresholdHC.CriticalUpper.ScreenCoin
import ThresholdHC.CriticalUpper.WeightedCost
import ThresholdHC.CriticalEntropy.PopulationMixture

/-! Population error and expected-work inequalities for every measurable rare prior. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem measurable_tape_integral (F : (ℕ → Bool) → ℝ) (hF : Measurable F) :
    Measurable (fun p : unitInterval => ∫ ω, F ω ∂Tier2.tapeMeasure p) := by
  have hm := (hF.comp measurable_uniformCoinTape).stronglyMeasurable.integral_prod_right'
    (ν := uniformTapeMeasure)
  convert hm.measurable using 1
  funext p
  rw [← uniformCoinTape_map p]
  exact integral_map (measurable_uniformCoinTape.comp
    (measurable_const.prodMk measurable_id)).aemeasurable hF.aestronglyMeasurable

def screenConditionalError (A₀ A₁ : ℝ) (L : ℕ) (b : Bool) (d : ℝ) : ℝ :=
  (Tier2.tapeMeasure (criticalParameter d b)).real {ω | screenValue A₀ A₁ L ω ≠ Tier2.bit b}

theorem screenConditionalError_integral (A₀ A₁ : ℝ) (L : ℕ) (b : Bool) (d : ℝ) :
    screenConditionalError A₀ A₁ L b d =
      ∫ ω, |screenValue A₀ A₁ L ω-Tier2.bit b| ∂Tier2.tapeMeasure (criticalParameter d b) := by
  have he : (fun ω => |screenValue A₀ A₁ L ω-Tier2.bit b|) =
      {ω | screenValue A₀ A₁ L ω ≠ Tier2.bit b}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rcases screenDecision_zero_or_one A₀ A₁ (fun k => dyadicMean Tier2.observations k ω) L with h | h
    all_goals change screenValue A₀ A₁ L ω = _ at h
    all_goals cases b <;> simp [h,Tier2.bit,Set.indicator_apply]
  have hs : MeasurableSet {ω | screenValue A₀ A₁ L ω ≠ Tier2.bit b} :=
    (measurableSet_eq_fun (measurable_screenValue A₀ A₁ L) measurable_const).compl
  rw [he,integral_indicator_const (1 : ℝ) hs]
  simp [screenConditionalError]

theorem measurable_screenConditionalError (A₀ A₁ : ℝ) (L : ℕ) (b : Bool) :
    Measurable (screenConditionalError A₀ A₁ L b) := by
  have hm := (measurable_tape_integral (fun ω => |screenValue A₀ A₁ L ω-Tier2.bit b|)
    (((measurable_screenValue A₀ A₁ L).sub measurable_const).abs)).comp
      (measurable_criticalParameter b)
  simpa only [Function.comp_def,← screenConditionalError_integral] using hm

theorem screenConditionalError_nonneg (A₀ A₁ : ℝ) (L : ℕ) (b : Bool) (d : ℝ) :
    0 ≤ screenConditionalError A₀ A₁ L b d := measureReal_nonneg

theorem screenConditionalError_le_one (A₀ A₁ : ℝ) (L : ℕ) (b : Bool) (d : ℝ) :
    screenConditionalError A₀ A₁ L b d ≤ 1 := measureReal_le_one

theorem integrable_unitPrior (q : ℝ → unitInterval) (hq : Measurable q) :
    Integrable (fun d => (q d : ℝ)) criticalGapLaw := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q d).property.1]; exact (q d).property.2)

theorem integrable_prior_screen_error (A₀ A₁ : ℝ) (L : ℕ) (b : Bool)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    Integrable (fun d => (q d : ℝ)*screenConditionalError A₀ A₁ L b d) criticalGapLaw := by
  apply Integrable.of_bound
    (((measurable_subtype_coe.comp hq).mul (measurable_screenConditionalError A₀ A₁ L b)).aestronglyMeasurable) 1
  exact ae_of_all _ (fun d => by
    change ‖(q d : ℝ)*screenConditionalError A₀ A₁ L b d‖ ≤ 1
    rw [Real.norm_of_nonneg (mul_nonneg (q d).property.1 (screenConditionalError_nonneg A₀ A₁ L b d))]
    exact (mul_le_mul_of_nonneg_left (screenConditionalError_le_one A₀ A₁ L b d)
      (q d).property.1).trans (by simpa using (q d).property.2))

def screenPopulationError (A₀ A₁ : ℝ) (L : ℕ) (q : ℝ → unitInterval) : ℝ :=
  ∫ d, (q d : ℝ)*screenConditionalError A₀ A₁ L true d +
    (1-(q d : ℝ))*screenConditionalError A₀ A₁ L false d ∂criticalGapLaw

theorem screen_population_error_le (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (L : ℕ) (ρ : ℝ) (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    screenPopulationError A₀ A₁ L q ≤
      8/cap L+ρ*((L : ℝ)*Real.exp (-A₀))+(L : ℝ)*Real.exp (-A₁) := by
  have hneg : Integrable (fun d => (1-(q d : ℝ))*screenConditionalError A₀ A₁ L false d)
      criticalGapLaw := by
    simpa only [unitInterval.coe_symm_eq] using
      integrable_prior_screen_error A₀ A₁ L false (fun d => unitInterval.symm (q d))
        (unitInterval.continuous_symm.measurable.comp hq)
  have hleft := (integrable_prior_screen_error A₀ A₁ L true q hq).add hneg
  have hright := ((criticalGaussian_integrable (cap L) (cap_pos L)).add
    ((integrable_unitPrior q hq).mul_const ((L : ℝ)*Real.exp (-A₀)))).add
      (integrable_const ((L : ℝ)*Real.exp (-A₁)))
  have hpoint : (fun d => (q d : ℝ)*screenConditionalError A₀ A₁ L true d +
      (1-(q d : ℝ))*screenConditionalError A₀ A₁ L false d) ≤ᵐ[criticalGapLaw]
      fun d => Real.exp (-2*cap L*d^2)+(q d : ℝ)*((L : ℝ)*Real.exp (-A₀))+
        (L : ℝ)*Real.exp (-A₁) := by
    filter_upwards [criticalGap_ae_support] with d hd
    have hp := screen_coin_error A₀ A₁ hA₀ hA₁ L d hd true
    have hn := screen_coin_error A₀ A₁ hA₀ hA₁ L d hd false
    simp only [ite_true,Bool.false_eq_true,ite_false] at hp hn
    change screenConditionalError A₀ A₁ L true d ≤ _ at hp
    change screenConditionalError A₀ A₁ L false d ≤ _ at hn
    have hp' := mul_le_mul_of_nonneg_left hp (q d).property.1
    have hn' := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr (q d).property.2)
    have hterm : 0 ≤ (q d : ℝ)*((L : ℝ)*Real.exp (-A₁)) :=
      mul_nonneg (q d).property.1 (by positivity)
    nlinarith
  have hi := integral_mono_ae hleft hright hpoint
  simp only [Pi.add_apply] at hi
  have he := integral_add ((criticalGaussian_integrable (cap L) (cap_pos L)).add
      ((integrable_unitPrior q hq).mul_const ((L : ℝ)*Real.exp (-A₀))))
      (integrable_const (μ := criticalGapLaw) ((L : ℝ)*Real.exp (-A₁)))
  have he' := integral_add (criticalGaussian_integrable (cap L) (cap_pos L))
      ((integrable_unitPrior q hq).mul_const ((L : ℝ)*Real.exp (-A₀)))
  simp only [Pi.add_apply] at he he'
  rw [he,he',integral_mul_const,integral_const] at hi
  simp only [probReal_univ,smul_eq_mul,one_mul] at hi
  have hm := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ (L : ℝ)*Real.exp (-A₀))
  have hg := criticalGaussian_integral_le (cap L) (cap_pos L)
  exact hi.trans (by linarith)

theorem integrable_prior_cappedCost (N K : ℝ) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    Integrable (fun d => (q d : ℝ)*criticalCappedCost N K d) criticalGapLaw := by
  apply Integrable.of_bound (by unfold criticalCappedCost; fun_prop) N
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (mul_nonneg (q d).property.1 (criticalCappedCost_nonneg N K d hN hK))]
    exact (mul_le_mul_of_nonneg_right (q d).property.2
      (criticalCappedCost_nonneg N K d hN hK)).trans
        (by simpa [criticalCappedCost] using (min_le_left N (K/(16*d^2)))))

theorem criticalCappedCost_integral_le (N K : ℝ) (hN : 0 < N) (hK : 0 < K) :
    (∫ d, criticalCappedCost N K d ∂criticalGapLaw) ≤
      K*(2+max 0 (Real.log (N/K))) := by
  simpa using criticalCappedCost_weighted_le N K 1 hN hK (by norm_num) le_rfl
    (fun _ => 1) measurable_const (by simp)

theorem screen_coin_capped_work (A₀ A₁ : ℝ) (hA₀ : 1 ≤ A₀) (hA₁ : 1 ≤ A₁)
    (L : ℕ) (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1/4)) (b : Bool) :
    expectedStoppedProcedureWork (Measure.dirac ()) (criticalParameter d b) (screenProcedure A₀ A₁ L) ≤
      ENNReal.ofReal (criticalCappedCost (cap L) (160*(if b then A₁ else A₀)) d) := by
  have he : 160*(if b then A₁ else A₀)/(16*d^2) = 10*(if b then A₁ else A₀)/d^2 := by ring
  simpa only [criticalCappedCost,he] using screen_coin_work A₀ A₁ hA₀ hA₁ L d hd b

/-- The positive contribution uses only total prior mass, including priors
concentrated on the smallest gaps. Cost is the actual stopped flip count. -/
theorem screen_population_work_le (A₀ A₁ : ℝ) (hA₀ : 1 ≤ A₀) (hA₁ : 1 ≤ A₁)
    (L : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    populationExpectedWork criticalGapLaw (Measure.dirac ())
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q
      (screenProcedure A₀ A₁ L) ≤
    ENNReal.ofReal (160*A₀*(2+max 0 (Real.log (cap L/(160*A₀))))+
      160*A₁*(2+max 0 (Real.log (cap L*ρ/(160*A₁))))) := by
  let f₀ := criticalCappedCost (cap L) (160*A₀)
  let f₁ := criticalCappedCost (cap L) (160*A₁)
  have hK₀ : 0 < 160*A₀ := by linarith
  have hK₁ : 0 < 160*A₁ := by linarith
  have hf₀ (d : ℝ) : 0 ≤ f₀ d := criticalCappedCost_nonneg _ _ _ (cap_pos L).le hK₀.le
  have hf₁ (d : ℝ) : 0 ≤ f₁ d := criticalCappedCost_nonneg _ _ _ (cap_pos L).le hK₁.le
  have hi₀ := criticalCappedCost_integrable (cap L) (160*A₀) (cap_pos L).le hK₀.le
  have hi₁ := integrable_prior_cappedCost (cap L) (160*A₁) (cap_pos L).le hK₁.le q hq
  have hg (d : ℝ) : 0 ≤ (q d : ℝ)*f₁ d+f₀ d :=
    add_nonneg (mul_nonneg (q d).property.1 (hf₁ d)) (hf₀ d)
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal ((q d : ℝ)*f₁ d+f₀ d) ∂criticalGapLaw := by
      rw [population_work_formula criticalGapLaw (Measure.dirac ()) _ _ q
        (measurable_criticalParameter false) (measurable_criticalParameter true) hq]
      apply lintegral_mono_ae
      filter_upwards [criticalGap_ae_support] with d hd
      have hp := screen_coin_capped_work A₀ A₁ hA₀ hA₁ L d hd true
      have hn := screen_coin_capped_work A₀ A₁ hA₀ hA₁ L d hd false
      simp only [ite_true,Bool.false_eq_true,ite_false] at hp hn
      have hcoeff : ENNReal.ofReal (1-(q d : ℝ)) ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal (sub_le_self (1 : ℝ) (q d).property.1)
      have hb := add_le_add (mul_le_mul' (le_refl (ENNReal.ofReal (q d : ℝ))) hp) (mul_le_mul' hcoeff hn)
      rw [one_mul] at hb
      apply hb.trans_eq
      rw [ENNReal.ofReal_add (mul_nonneg (q d).property.1 (hf₁ d)) (hf₀ d),
        ENNReal.ofReal_mul (q d).property.1]
    _ = ENNReal.ofReal (∫ d, (q d : ℝ)*f₁ d+f₀ d ∂criticalGapLaw) :=
      (ofReal_integral_eq_lintegral_ofReal (hi₁.add hi₀) (ae_of_all _ hg)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_add hi₁ hi₀]
      have hp := criticalCappedCost_weighted_le (cap L) (160*A₁) ρ (cap_pos L) hK₁ hρ hρ1 q hq hmass
      have hn := criticalCappedCost_integral_le (cap L) (160*A₀) (cap_pos L) hK₀
      linarith

end ThresholdHC.CriticalUpper
