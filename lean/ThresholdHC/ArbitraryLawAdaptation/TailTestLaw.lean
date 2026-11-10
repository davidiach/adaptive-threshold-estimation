import ThresholdHC.ArbitraryLawAdaptation.TailTestProbability
import ThresholdHC.ArbitraryLawAdaptation.LightMultiplier

/-! The tail test on one fresh population coin, for every sign law.

Complementing every flip exchanges the two signs of a coin and leaves the test
unchanged. Hence the law of the test on a coin of the original population
depends on the gap law only, whatever measurable gap-dependent sign law the
population has. The single-coin bounds then integrate over an arbitrary
probability law of positive gaps, with no inverse-moment assumption. -/

noncomputable section
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

/-- Complementing every flip exchanges the two signs of a coin. -/
theorem tapeMeasure_flip (p : unitInterval) :
    (tapeMeasure p).map tapeFlip = tapeMeasure (unitInterval.symm p) := by
  unfold tapeMeasure tapeFlip
  rw [Measure.infinitePi_map_pi (f := fun _ (b : Bool) => !b) _
    (fun _ => measurable_of_countable _)]
  congr 1
  funext _
  rw [map_bernoulliMeasure]
  simp only [Bool.not_true, Bool.not_false, bernoulliMeasure_def, unitInterval.symm_symm]
  rw [add_comm]

theorem gapParameter_false_eq (d : Gap) :
    gapParameter false d = unitInterval.symm (gapParameter true d) := by
  apply Subtype.ext
  simp [gapParameter]
  ring

/-- A flip-invariant event has the same probability under both signs. -/
theorem tapeMeasure_flip_invariant (d : Gap) {S : Set (ℕ → Bool)} (hS : MeasurableSet S)
    (hflip : tapeFlip ⁻¹' S = S) :
    tapeMeasure (gapParameter false d) S = tapeMeasure (gapParameter true d) S := by
  rw [gapParameter_false_eq, ← tapeMeasure_flip, Measure.map_apply measurable_tapeFlip hS, hflip]

/-- A flip-invariant statistic has the same mean under both signs. -/
theorem tape_integral_flip (p : unitInterval) (G : (ℕ → Bool) → ℝ) (hG : Measurable G)
    (hflip : ∀ t, G (tapeFlip t) = G t) :
    ∫ t, G t ∂tapeMeasure (unitInterval.symm p) = ∫ t, G t ∂tapeMeasure p := by
  rw [← tapeMeasure_flip, integral_map measurable_tapeFlip.aemeasurable hG.aestronglyMeasurable]
  simp_rw [hflip]

/-- The complete stopping path has the same law under both signs. -/
theorem tailStop_law_sign_neutral (J : ℕ) (d : Gap) :
    (tapeMeasure (gapParameter false d)).map (tailStop J) =
      (tapeMeasure (gapParameter true d)).map (tailStop J) := by
  rw [gapParameter_false_eq, ← tapeMeasure_flip,
    Measure.map_map (measurable_tailStop J) measurable_tapeFlip]
  congr 1
  funext ω
  exact tailStop_flip J ω

theorem tailUnresolved_flip_preimage (J : ℕ) :
    tapeFlip ⁻¹' {ω | tailUnresolved J ω} = {ω | tailUnresolved J ω} := by
  ext ω
  exact tailUnresolved_flip J ω

/-- The unresolved probability is the same under both signs. -/
theorem tailUnresolved_sign_neutral (J : ℕ) (d : Gap) :
    tapeMeasure (gapParameter false d) {ω | tailUnresolved J ω} =
      tapeMeasure (gapParameter true d) {ω | tailUnresolved J ω} :=
  tapeMeasure_flip_invariant d (measurableSet_tailUnresolved J) (tailUnresolved_flip_preimage J)

theorem parameterTape_integral (κ : Measure unitInterval) [IsProbabilityMeasure κ]
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) {M : ℝ} (hb : ∀ t, |F t| ≤ M) :
    (∫ t, F t ∂parameterTapeLaw κ) = ∫ p, (∫ t, F t ∂tapeMeasure p) ∂κ := by
  have hi := ThresholdHC.Tier5.integrable_of_abs_bound (κ.prod uniformTapeMeasure)
    (fun z => F (uniformCoinTape z.1 z.2)) (hF.comp measurable_uniformCoinTape) M
    (fun _ => hb _)
  rw [parameterTapeLaw, integral_map measurable_uniformCoinTape.aemeasurable
    hF.aestronglyMeasurable, integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  change (∫ u, F (uniformCoinTape p u) ∂uniformTapeMeasure) = ∫ t, F t ∂tapeMeasure p
  have hm : Measurable (uniformCoinTape p) :=
    measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
  rw [← uniformCoinTape_map p]
  exact (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm

theorem measurable_tape_integral (F : (ℕ → Bool) → ℝ) (hF : Measurable F) :
    Measurable (fun p : unitInterval => ∫ t, F t ∂tapeMeasure p) := by
  have h : (fun p : unitInterval => ∫ t, F t ∂tapeMeasure p) =
      fun p => ∫ u, F (uniformCoinTape p u) ∂uniformTapeMeasure := by
    funext p
    have hm : Measurable (uniformCoinTape p) :=
      measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
    rw [← uniformCoinTape_map p, integral_map hm.aemeasurable hF.aestronglyMeasurable]
  rw [h]
  exact ((hF.comp measurable_uniformCoinTape).stronglyMeasurable.integral_prod_right').measurable

theorem tape_integral_abs_le (p : unitInterval) (G : (ℕ → Bool) → ℝ) {M : ℝ}
    (hb : ∀ t, |G t| ≤ M) : |∫ t, G t ∂tapeMeasure p| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := tapeMeasure p) (f := G) (C := M)
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hb t)
  simpa using h

/-- Sign neutrality on the original population. For a bounded statistic of one
coin's tape that is invariant under complementing every flip, the mean under
the actual population tape law depends on the gap law only: every measurable
gap-dependent sign law gives the same value. -/
theorem original_tape_integral_sign_neutral (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (G : (ℕ → Bool) → ℝ) (hG : Measurable G) {M : ℝ} (hb : ∀ t, |G t| ≤ M)
    (hflip : ∀ t, G (tapeFlip t) = G t) :
    ∫ t, G t ∂originalPopulationTapeLaw μ q =
      ∫ d, (∫ t, G t ∂tapeMeasure (gapParameter true d)) ∂μ := by
  let κ := populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit q)
  let : IsProbabilityMeasure κ := populationParameterLaw_probability μ
    (gapParameter false) (gapParameter true) (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  change (∫ t, G t ∂parameterTapeLaw κ) = _
  rw [parameterTape_integral κ G hG hb]
  rw [show κ = populationParameterLaw μ (gapParameter false) (gapParameter true)
      (signUnit q) from rfl,
    populationParameterLaw_integral μ _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit q)
      (fun p => ∫ t, G t ∂tapeMeasure p) (measurable_tape_integral G hG) M
      (fun p => tape_integral_abs_le p G hb)]
  apply integral_congr_ae
  apply ae_of_all
  intro d
  dsimp only
  rw [gapParameter_false_eq, tape_integral_flip _ G hG hflip]
  ring

/-- Probability that the test leaves a coin of gap `d` unresolved. -/
def tailUnresolvedProb (J : ℕ) (d : Gap) : ℝ :=
  (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω}

/-- `u_J`: the unresolved probability of one fresh coin with gap law `μ`. -/
def tailUnresolvedMass (μ : Measure Gap) (J : ℕ) : ℝ := ∫ d, tailUnresolvedProb J d ∂μ

theorem tailUnresolvedProb_eq_integral (J : ℕ) (d : Gap) :
    tailUnresolvedProb J d = ∫ t, Set.indicator {ω | tailUnresolved J ω} (fun _ => (1 : ℝ)) t
      ∂tapeMeasure (gapParameter true d) := by
  rw [integral_indicator (measurableSet_tailUnresolved J), setIntegral_const]
  simp [tailUnresolvedProb]

theorem measurable_tailUnresolvedProb (J : ℕ) : Measurable (tailUnresolvedProb J) := by
  have h : tailUnresolvedProb J = (fun p : unitInterval =>
      ∫ t, Set.indicator {ω | tailUnresolved J ω} (fun _ => (1 : ℝ)) t ∂tapeMeasure p) ∘
        gapParameter true := by
    funext d
    exact tailUnresolvedProb_eq_integral J d
  rw [h]
  exact (measurable_tape_integral _
    (measurable_const.indicator (measurableSet_tailUnresolved J))).comp
      (measurable_gapParameter true)

theorem tailUnresolvedProb_nonneg (J : ℕ) (d : Gap) : 0 ≤ tailUnresolvedProb J d :=
  measureReal_nonneg

theorem tailUnresolvedProb_le_one (J : ℕ) (d : Gap) : tailUnresolvedProb J d ≤ 1 :=
  measureReal_le_one

theorem integrable_tailUnresolvedProb (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ) :
    Integrable (tailUnresolvedProb J) μ :=
  ThresholdHC.Tier5.integrable_of_abs_bound μ _ (measurable_tailUnresolvedProb J) 1 fun d => by
    rw [abs_of_nonneg (tailUnresolvedProb_nonneg J d)]
    exact tailUnresolvedProb_le_one J d

/-- On the original population the unresolved probability of a fresh coin is
`u_J`, for every sign law. -/
theorem original_tail_unresolved (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J : ℕ) :
    (originalPopulationTapeLaw μ q).real {ω | tailUnresolved J ω} = tailUnresolvedMass μ J := by
  have hS := measurableSet_tailUnresolved J
  have h := original_tape_integral_sign_neutral μ q
    (Set.indicator {ω | tailUnresolved J ω} (fun _ => (1 : ℝ)))
    (measurable_const.indicator hS) (M := 1)
    (fun t => by
      by_cases ht : t ∈ {ω | tailUnresolved J ω}
      · rw [Set.indicator_of_mem ht]; norm_num
      · rw [Set.indicator_of_notMem ht]; norm_num)
    (fun t => by
      have hiff : tapeFlip t ∈ {ω | tailUnresolved J ω} ↔ t ∈ {ω | tailUnresolved J ω} :=
        tailUnresolved_flip J t
      by_cases ht : t ∈ {ω | tailUnresolved J ω}
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hiff.2 ht)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun h' => ht (hiff.1 h'))])
  rw [integral_indicator hS, setIntegral_const] at h
  simp only [smul_eq_mul, mul_one] at h
  rw [h]
  unfold tailUnresolvedMass
  exact integral_congr_ae (ae_of_all _ fun d => (tailUnresolvedProb_eq_integral J d).symm)

/-- The lower half of (2): `F(2^{-J})/2 ≤ u_J`. -/
theorem tail_unresolved_mass_lower (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ) :
    μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} / 2 ≤ tailUnresolvedMass μ J := by
  have hA : MeasurableSet {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} :=
    measurableSet_le measurable_subtype_coe measurable_const
  have hint : Integrable
      (Set.indicator {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} (fun _ => (1 / 2 : ℝ))) μ :=
    (integrable_const (1 / 2 : ℝ)).indicator hA
  have hmono := integral_mono hint (integrable_tailUnresolvedProb μ J) (fun d => by
    by_cases hd : d ∈ {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J}
    · rw [Set.indicator_of_mem hd]
      exact tail_unresolved_ge_half J d hd
    · rw [Set.indicator_of_notMem hd]
      exact tailUnresolvedProb_nonneg J d)
  rw [integral_indicator hA, setIntegral_const] at hmono
  unfold tailUnresolvedMass
  simp only [smul_eq_mul] at hmono
  linarith

theorem tailUnresolvedProb_le_exp (J : ℕ) (d : Gap) (hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ)) :
    tailUnresolvedProb J d ≤ exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) :=
  tail_unresolved_le_exp J d hd

theorem four_pow_half_pow (J : ℕ) : (4 : ℝ) ^ J * ((1 / 2 : ℝ) ^ J) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm J 2, pow_mul, ← mul_pow]
  norm_num

/-- The pointwise envelope `u_J(d) ≤ min{1, 16 (t/d)²}` at `t = 2^{-J}`. -/
theorem tailUnresolvedProb_le_envelope (J : ℕ) (d : Gap) :
    tailUnresolvedProb J d ≤ min 1 (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2) := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have ht0 : (0 : ℝ) < (1 / 2) ^ J := by positivity
  refine le_min (tailUnresolvedProb_le_one J d) ?_
  by_cases hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ)
  · have hx : (0 : ℝ) < 4 ^ J * (d : ℝ) ^ 2 / 2 := by positivity
    have hexp : exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) ≤ (4 ^ J * (d : ℝ) ^ 2 / 2)⁻¹ := by
      rw [exp_neg]
      exact inv_anti₀ hx (by linarith [add_one_le_exp (4 ^ J * (d : ℝ) ^ 2 / 2)])
    have heq : (4 ^ J * (d : ℝ) ^ 2 / 2)⁻¹ = 2 * ((1 / 2) ^ J / (d : ℝ)) ^ 2 := by
      have h := four_pow_half_pow J
      have h4 : (0 : ℝ) < 4 ^ J := by positivity
      field_simp
      nlinarith
    have hnn : (0 : ℝ) ≤ ((1 / 2) ^ J / (d : ℝ)) ^ 2 := by positivity
    calc tailUnresolvedProb J d ≤ exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) :=
          tailUnresolvedProb_le_exp J d hd
      _ ≤ (4 ^ J * (d : ℝ) ^ 2 / 2)⁻¹ := hexp
      _ = 2 * ((1 / 2) ^ J / (d : ℝ)) ^ 2 := heq
      _ ≤ 16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2 := by linarith
  · have hlt : (d : ℝ) < 4 * (1 / 2 : ℝ) ^ J := not_le.mp hd
    have hq : (1 : ℝ) / 4 < (1 / 2) ^ J / (d : ℝ) := by
      rw [lt_div_iff₀ hd0]
      linarith
    have hsq : (1 : ℝ) / 16 < ((1 / 2) ^ J / (d : ℝ)) ^ 2 := by nlinarith
    linarith [tailUnresolvedProb_le_one J d]

/-- The upper half of (2): `u_J ≤ ∫ min{1, 16 (t/d)²} dμ`. -/
theorem tail_unresolved_mass_upper (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ) :
    tailUnresolvedMass μ J ≤ ∫ d : Gap, min 1 (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2) ∂μ := by
  have hm : Measurable (fun d : Gap => min (1 : ℝ) (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2)) :=
    measurable_const.min ((measurable_const.div measurable_subtype_coe).pow_const 2
      |>.const_mul 16)
  have hint : Integrable (fun d : Gap => min (1 : ℝ) (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2)) μ :=
    ThresholdHC.Tier5.integrable_of_abs_bound μ _ hm 1 fun d => by
      rw [abs_of_nonneg (le_min zero_le_one (by positivity))]
      exact min_le_left _ _
  exact integral_mono (integrable_tailUnresolvedProb μ J) hint
    (fun d => tailUnresolvedProb_le_envelope J d)

/-- The sharper terminal bound against the constructed multiplier: pointwise,
`u_J(d) ≤ G_V(t/d)`. -/
theorem tailUnresolvedProb_le_lightCDF (J : ℕ) (d : Gap) :
    tailUnresolvedProb J d ≤ lightCDF ((1 / 2) ^ J / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have hx : (0 : ℝ) < (1 / 2) ^ J / (d : ℝ) := by positivity
  unfold lightCDF
  rw [ite_eq_right (not_le.mpr hx)]
  by_cases hq : (1 / 2 : ℝ) ^ J / (d : ℝ) < 1 / 4
  · rw [ite_eq_left hq]
    have hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ) := by
      rw [div_lt_iff₀ hd0] at hq
      linarith
    have heq : 1 / (2 * ((1 / 2 : ℝ) ^ J / (d : ℝ)) ^ 2) = 4 ^ J * (d : ℝ) ^ 2 / 2 := by
      have h := four_pow_half_pow J
      have ht : (0 : ℝ) < (1 / 2) ^ J := by positivity
      field_simp
      nlinarith
    rw [heq]
    have hpos := exp_pos (-(4 ^ J * (d : ℝ) ^ 2 / 2))
    linarith [tailUnresolvedProb_le_exp J d hd]
  · rw [ite_eq_right hq]
    exact tailUnresolvedProb_le_one J d

/-- `u_J ≤ P(V D ≤ 2^{-J})` for the constructed multiplier `V`, independent of
`D ∼ μ`. This is the terminal estimate used by the learned-law comparison. -/
theorem tail_unresolved_mass_le_multiplier (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ) :
    ENNReal.ofReal (tailUnresolvedMass μ J) ≤
      (μ.prod lightMultiplier) {z : Gap × Gap | (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ J} := by
  have hS : MeasurableSet {z : Gap × Gap | (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ J} :=
    measurableSet_le ((measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply hS]
  unfold tailUnresolvedMass
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_tailUnresolvedProb μ J)
    (ae_of_all _ fun d => tailUnresolvedProb_nonneg J d)]
  apply lintegral_mono
  intro d
  have hd0 : (0 : ℝ) < d := d.property.1
  have hsec : Prod.mk d ⁻¹' {z : Gap × Gap | (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ J} =
      {v : Gap | (v : ℝ) ≤ (1 / 2) ^ J / (d : ℝ)} := by
    ext v
    change (d : ℝ) * (v : ℝ) ≤ (1 / 2) ^ J ↔ (v : ℝ) ≤ (1 / 2) ^ J / (d : ℝ)
    rw [le_div_iff₀ hd0, mul_comm]
  beta_reduce
  rw [hsec, lightMultiplier_cdf]
  exact ENNReal.ofReal_le_ofReal (tailUnresolvedProb_le_lightCDF J d)

theorem tailLog_nonneg (J : ℕ) (d : ℝ) : 0 ≤ tailLog J d := le_max_left _ _

theorem tailWorkEnvelope_le (J : ℕ) (d : ℝ) : tailWorkEnvelope J d ≤ 4 ^ J := min_le_left _ _

theorem tailWorkEnvelope_nonneg (J : ℕ) (d : ℝ) : 0 ≤ tailWorkEnvelope J d := by
  unfold tailWorkEnvelope
  have h := tailLog_nonneg J d
  exact le_min (by positivity) (by positivity)

theorem measurable_tailWorkEnvelope (J : ℕ) : Measurable (tailWorkEnvelope J) := by
  unfold tailWorkEnvelope tailLog
  have hlog : Measurable (fun d : ℝ => Real.logb 2 (d * 2 ^ J)) := by
    unfold Real.logb
    exact (Real.measurable_log.comp (measurable_id.mul_const _)).div_const _
  exact measurable_const.min
    ((measurable_const.div (measurable_id.pow_const 2)).mul
      (measurable_const.add (measurable_const.max hlog)))

/-- The work bound under either sign. -/
theorem tail_expected_work_le_sign (J : ℕ) (s : Bool) (d : Gap) :
    ∫ ω, (tailWork J ω : ℝ) ∂tapeMeasure (gapParameter s d) ≤ tailWorkEnvelope J d := by
  cases s
  · rw [gapParameter_false_eq, tape_integral_flip _ (fun ω => (tailWork J ω : ℝ))
      ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_tailWork J))
      (fun t => by rw [tailWork_flip])]
    exact tail_expected_work_le J d
  · exact tail_expected_work_le J d

/-- (4) integrated: on the original population the expected work on one fresh
coin is at most `W_J = ∫ w_J dμ`, for every sign law and every probability law
of positive gaps. -/
theorem original_tail_expected_work (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J : ℕ) :
    ∫ t, (tailWork J t : ℝ) ∂originalPopulationTapeLaw μ q ≤
      ∫ d : Gap, tailWorkEnvelope J d ∂μ := by
  have hmw : Measurable (fun ω : ℕ → Bool => (tailWork J ω : ℝ)) :=
    (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_tailWork J)
  have hbw : ∀ t : ℕ → Bool, |(tailWork J t : ℝ)| ≤ 4 ^ J := fun t => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast tailWork_le J t
  rw [original_tape_integral_sign_neutral μ q _ hmw hbw (fun t => by rw [tailWork_flip])]
  have hl : Integrable
      (fun d : Gap => ∫ t, (tailWork J t : ℝ) ∂tapeMeasure (gapParameter true d)) μ :=
    ThresholdHC.Tier5.integrable_of_abs_bound μ _
      ((measurable_tape_integral _ hmw).comp (measurable_gapParameter true)) (4 ^ J)
      (fun d => tape_integral_abs_le _ _ hbw)
  have hr : Integrable (fun d : Gap => tailWorkEnvelope J d) μ :=
    ThresholdHC.Tier5.integrable_of_abs_bound μ _
      ((measurable_tailWorkEnvelope J).comp measurable_subtype_coe) (4 ^ J) fun d => by
        rw [abs_of_nonneg (tailWorkEnvelope_nonneg J d)]
        exact tailWorkEnvelope_le J d
  exact integral_mono hl hr fun d => tail_expected_work_le J d

end ThresholdHC.ArbitraryLawAdaptation
