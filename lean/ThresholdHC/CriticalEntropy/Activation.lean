import ThresholdHC.CriticalEntropy.ActivationModel
import ThresholdHC.CriticalEntropy.GoodGaps

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem measurableSet_activeSeeds {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) : MeasurableSet (activeSeeds A) := by
  exact (measurableSet_eq_fun
    (A.measurable_stop.comp (measurable_id.prodMk measurable_const)) measurable_const).compl

theorem stop_zero_iff_inactive {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (r : R) (ω : ℕ → Bool) :
    A.stop (r,ω) = 0 ↔ r ∉ activeSeeds A := by
  have hp : Tier2.tapePrefix 0 ω = Tier2.tapePrefix 0 (fun _ => false) := Subsingleton.elim _ _
  constructor
  · intro h
    exact not_not.mpr (stopped_prefix_ext A r ω (fun _ => false) 0 hp h).1
  · intro h
    have h' : A.stop (r,fun _ => false) = 0 := not_not.mp h
    exact (stopped_prefix_ext A r (fun _ => false) ω 0 hp.symm h').1

theorem inactive_output {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (r : R) (ω : ℕ → Bool) (h : r ∉ activeSeeds A) :
    A.output (r,ω) = A.output (r,fun _ => false) := by
  exact (stopped_prefix_ext A r (fun _ => false) ω 0 (Subsingleton.elim _ _)
    (not_not.mp h)).2

theorem inactive_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (r : R) (ω : ℕ → Bool) (h : r ∉ activeSeeds A) :
    stoppedProcedureWork A (r,ω) = 0 := by
  simp [stoppedProcedureWork,(stop_zero_iff_inactive A r ω).mpr h]

theorem active_work_lower {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (r : R) (ω : ℕ → Bool) (h : r ∈ activeSeeds A) :
    1 ≤ stoppedProcedureWork A (r,ω) := by
  have hn : A.stop (r,ω) ≠ 0 := by
    intro hz
    exact (stop_zero_iff_inactive A r ω).mp hz h
  have hl : (1 : ℕ∞) ≤ A.stop (r,ω) := Order.one_le_iff_ne_zero.mpr hn
  change (1 : ℝ≥0∞) ≤ (A.stop (r,ω)).toENNReal
  simpa using ENat.toENNReal_mono hl

theorem activation_work_restrict {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R E) :
    (∫⁻ z in activeSeeds A ×ˢ univ, stoppedProcedureWork A z ∂ν.prod (Tier2.tapeMeasure p)) =
      expectedStoppedProcedureWork ν p A := by
  rw [← lintegral_indicator ((measurableSet_activeSeeds A).prod MeasurableSet.univ)]
  apply lintegral_congr
  intro z
  by_cases h : z.1 ∈ activeSeeds A
  · simp [h]
  · simp [h,inactive_work A z.1 z.2 h]

theorem activation_conditional_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R E) :
    expectedStoppedProcedureWork (cond ν (activeSeeds A)) p A =
      (ν (activeSeeds A))⁻¹*expectedStoppedProcedureWork ν p A := by
  unfold expectedStoppedProcedureWork
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,lintegral_smul_measure,
    Measure.restrict_prod_eq_prod_univ,activation_work_restrict]
  rfl

theorem activation_probability_le_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R E) :
    ν (activeSeeds A) ≤ expectedStoppedProcedureWork ν p A := by
  have hm : MeasurableSet (activeSeeds A ×ˢ (univ : Set (ℕ → Bool))) :=
    (measurableSet_activeSeeds A).prod MeasurableSet.univ
  calc
    _ = ∫⁻ z, (activeSeeds A ×ˢ univ).indicator (fun _ => (1 : ℝ≥0∞)) z
        ∂ν.prod (Tier2.tapeMeasure p) := by
      rw [lintegral_indicator hm,lintegral_const,Measure.restrict_apply_univ,Measure.prod_prod]
      simp
    _ ≤ _ := lintegral_mono (fun z => by
      by_cases h : z.1 ∈ activeSeeds A
      · simpa [h] using active_work_lower A z.1 z.2 h
      · simp [h])

theorem activation_conditional_work_lower {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R E)
    (ha : ν (activeSeeds A) ≠ 0) :
    1 ≤ expectedStoppedProcedureWork (cond ν (activeSeeds A)) p A := by
  rw [activation_conditional_work]
  calc
    _ = (ν (activeSeeds A))⁻¹*ν (activeSeeds A) :=
      (ENNReal.inv_mul_cancel ha (measure_ne_top _ _)).symm
    _ ≤ _ := mul_le_mul' le_rfl (activation_probability_le_work ν p A)

theorem normalized_event_mean {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (hpos : μ S ≠ 0) (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    (∫ z, μ.real S*Y z+(∫ x in Sᶜ, Y x ∂μ) ∂cond μ S) = ∫ x, Y x ∂μ := by
  let : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure hpos
  have hp : μ.real S ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos,measure_ne_top _ _⟩
  have hcond : MemLp Y 2 (cond μ S) :=
    (hY.restrict S).smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have hi := hcond.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [integral_add (hi.const_mul _) (integrable_const _),integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change μ.real S*((μ.real S)⁻¹*(∫ x in S, Y x ∂μ))+(∫ x in Sᶜ,Y x ∂μ) = _
  rw [← mul_assoc,mul_inv_cancel₀ hp,one_mul]
  exact integral_add_compl hS (hY.integrable (by norm_num))

theorem normalized_event_moment {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (hpos : μ S ≠ 0) (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    (∫ z, (μ.real S*Y z+(∫ x in Sᶜ, Y x ∂μ))^2 ∂cond μ S) ≤
      μ.real S*(∫ z, (Y z)^2 ∂μ)+(∫ z, Y z ∂μ)^2 := by
  let : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure hpos
  let p := μ.real S
  let c := ∫ x in Sᶜ,Y x ∂μ
  have hp : p ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos,measure_ne_top _ _⟩
  have hcond : MemLp Y 2 (cond μ S) :=
    (hY.restrict S).smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have hi := hcond.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsq := hcond.integrable_sq
  have hexpand : (∫ z, (p*Y z+c)^2 ∂cond μ S) =
      p^2*(∫ z, (Y z)^2 ∂cond μ S)+2*p*c*(∫ z,Y z ∂cond μ S)+c^2 := by
    calc
      _ = ∫ z, (p^2*(Y z)^2+(2*p*c)*Y z)+c^2 ∂cond μ S := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by ring)
      _ = _ := by
        have hi1 : Integrable (fun z => p^2*(Y z)^2+(2*p*c)*Y z) (cond μ S) :=
          (hsq.const_mul (p^2)).add (hi.const_mul (2*p*c))
        rw [integral_add hi1 (integrable_const (c^2)),
          integral_add (hsq.const_mul (p^2)) (hi.const_mul (2*p*c)),integral_const_mul,
          integral_const_mul,integral_const]
        simp
  have hspl := integral_add_compl hS (hY.integrable (by norm_num))
  have hraw : (∫ z, (p*Y z+c)^2 ∂cond μ S) =
      p*(∫ z in S,(Y z)^2 ∂μ)+2*c*(∫ z,Y z ∂μ)-c^2 := by
    rw [hexpand,ProbabilityTheory.cond,integral_smul_measure,integral_smul_measure]
    simp only [ENNReal.toReal_inv,smul_eq_mul]
    change p^2*(p⁻¹*(∫ z in S,(Y z)^2 ∂μ))+2*p*c*(p⁻¹*(∫ z in S,Y z ∂μ))+c^2 = _
    have ht : (∫ z in S,Y z ∂μ) = (∫ z,Y z ∂μ)-c := by linarith
    rw [ht]
    field_simp [hp]
    ring
  have hmon : (∫ z in S,(Y z)^2 ∂μ) ≤ ∫ z,(Y z)^2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hY.integrable_sq
  change (∫ z, (p*Y z+c)^2 ∂cond μ S) ≤ _
  rw [hraw]
  have hn := mul_le_mul_of_nonneg_left hmon (measureReal_nonneg (μ := μ) (s := S))
  nlinarith [sq_nonneg (c-(∫ z,Y z ∂μ))]

theorem measurableSet_populationSeedEvent {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    {S : Set R} (hS : MeasurableSet S) : MeasurableSet (populationSeedEvent (D := D) S) :=
  MeasurableSet.univ.prod (MeasurableSet.univ.prod (hS.prod MeasurableSet.univ))

theorem populationSeedEvent_measure {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (S : Set R) : populationMeasure μ ν (populationSeedEvent S) = ν S := by
  simp [populationMeasure,populationSeedEvent,Measure.prod_prod]

theorem populationMeasure_restrict_seed {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (S : Set R) : (populationMeasure μ ν).restrict (populationSeedEvent S) =
      populationMeasure μ (ν.restrict S) := by
  simp only [populationMeasure,populationSeedEvent,← Measure.prod_restrict,Measure.restrict_univ]

theorem populationMeasure_smul_seed {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsFiniteMeasure ν]
    (a : ℝ≥0∞) : populationMeasure μ (a • ν) = a • populationMeasure μ ν := by
  simp only [populationMeasure,Measure.prod_smul_left,Measure.prod_smul_right]

theorem populationMeasure_condition_seed {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (S : Set R) : cond (populationMeasure μ ν) (populationSeedEvent S) =
      populationMeasure μ (cond ν S) := by
  rw [ProbabilityTheory.cond,populationSeedEvent_measure,populationMeasure_restrict_seed,
    ProbabilityTheory.cond,populationMeasure_smul_seed]

theorem population_inactive_mean {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (A : StoppedProcedure R ℝ) :
    (∫ z in (populationSeedEvent (activeSeeds A))ᶜ,
      A.output (populationInput p₀ p₁ q z) ∂populationMeasure μ ν) =
      ∫ r in (activeSeeds A)ᶜ,A.output (r,fun _ => false) ∂ν := by
  have hE : MeasurableSet (populationSeedEvent (D := D) (activeSeeds A)) :=
    measurableSet_populationSeedEvent (measurableSet_activeSeeds A)
  have he : (populationSeedEvent (D := D) (activeSeeds A))ᶜ =
      populationSeedEvent (activeSeeds A)ᶜ := by
    ext z
    simp [populationSeedEvent]
  calc
    _ = ∫ z in (populationSeedEvent (activeSeeds A))ᶜ,
        A.output (z.2.2.1,fun _ => false) ∂populationMeasure μ ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hE.compl] with z hz
      have hz' : z.2.2.1 ∉ activeSeeds A := by simpa [populationSeedEvent] using hz
      exact inactive_output A z.2.2.1 _ hz'
    _ = _ := by
      rw [he,populationMeasure_restrict_seed]
      change (∫ z, A.output (z.2.2.1,fun _ => false)
        ∂μ.prod (uniformUnitMeasure.prod ((ν.restrict (activeSeeds A)ᶜ).prod uniformTapeMeasure))) = _
      rw [integral_fun_snd (fun z : ℝ × (R × (ℕ → ℝ)) => A.output (z.2.1,fun _ => false)),
        integral_fun_snd (fun z : R × (ℕ → ℝ) => A.output (z.1,fun _ => false)),
        integral_fun_fst (fun r : R => A.output (r,fun _ => false))]
      simp

theorem population_activation_mean {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R ℝ) (hpos : ν (activeSeeds A) ≠ 0)
    (hfin : populationSecondMoment μ ν p₀ p₁ q A ≠ ∞) :
    populationMean μ (cond ν (activeSeeds A)) p₀ p₁ q (activeProcedure ν A) =
      populationMean μ ν p₀ p₁ q A := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by unfold populationMeasure; infer_instance
  have hm := population_memLp_of_moment μ ν p₀ p₁ q h₀ h₁ hq A hfin
  have hs := measurableSet_populationSeedEvent (D := D) (measurableSet_activeSeeds A)
  have hp : populationMeasure μ ν (populationSeedEvent (activeSeeds A)) ≠ 0 := by
    rwa [populationSeedEvent_measure]
  have h := normalized_event_mean (populationMeasure μ ν) (populationSeedEvent (activeSeeds A))
    hs hp _ hm
  rw [populationMeasure_condition_seed,population_inactive_mean] at h
  have hreal : (populationMeasure μ ν).real (populationSeedEvent (activeSeeds A)) =
      ν.real (activeSeeds A) := by simp only [measureReal_def,populationSeedEvent_measure]
  rw [hreal] at h
  exact h

theorem population_activation_work {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R ℝ) (hpos : ν (activeSeeds A) ≠ 0) :
    populationExpectedWork μ (cond ν (activeSeeds A)) p₀ p₁ q (activeProcedure ν A) =
      (ν (activeSeeds A))⁻¹*populationExpectedWork μ ν p₀ p₁ q A := by
  let : IsProbabilityMeasure (cond ν (activeSeeds A)) := cond_isProbabilityMeasure hpos
  have hs : populationExpectedWork μ (cond ν (activeSeeds A)) p₀ p₁ q (activeProcedure ν A) =
      populationExpectedWork μ (cond ν (activeSeeds A)) p₀ p₁ q A := rfl
  rw [hs,population_work_formula μ (cond ν (activeSeeds A)) p₀ p₁ q h₀ h₁ hq A,
    population_work_formula μ ν p₀ p₁ q h₀ h₁ hq A]
  simp_rw [activation_conditional_work]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hpos)]
  apply lintegral_congr
  intro d
  ring

theorem activation_positive_of_bias {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ))
    (hb₀ : |populationMean μ ν p₀ p₁ (fun _ => 0) A| ≤ (ρ : ℝ)/64)
    (hb₁ : |populationMean μ ν p₀ p₁ (fun _ => ρ) A-(ρ : ℝ)| ≤ (ρ : ℝ)/64) :
    ν (activeSeeds A) ≠ 0 := by
  intro hzero
  have he : populationMeasure μ ν (populationSeedEvent (activeSeeds A)) = 0 := by
    rwa [populationSeedEvent_measure]
  have hr : (populationMeasure μ ν).restrict (populationSeedEvent (activeSeeds A))ᶜ =
      populationMeasure μ ν := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    simpa using he
  have hsame (q : D → unitInterval) : populationMean μ ν p₀ p₁ q A =
      ∫ r in (activeSeeds A)ᶜ,A.output (r,fun _ => false) ∂ν := by
    have h := population_inactive_mean μ ν p₀ p₁ q A
    rwa [hr] at h
  rw [hsame] at hb₀ hb₁
  have h0 := (abs_le.mp hb₀).2
  have h1 := (abs_le.mp hb₁).1
  linarith

theorem population_activation_moment {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R ℝ) (hpos : ν (activeSeeds A) ≠ 0)
    (hfin : populationSecondMoment μ ν p₀ p₁ q A ≠ ∞) :
    populationSecondMoment μ (cond ν (activeSeeds A)) p₀ p₁ q (activeProcedure ν A) ≤
      ENNReal.ofReal (ν.real (activeSeeds A)*(populationSecondMoment μ ν p₀ p₁ q A).toReal+
        (populationMean μ ν p₀ p₁ q A)^2) := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by unfold populationMeasure; infer_instance
  let : IsProbabilityMeasure (cond ν (activeSeeds A)) := cond_isProbabilityMeasure hpos
  let : IsProbabilityMeasure (populationMeasure μ (cond ν (activeSeeds A))) := by
    unfold populationMeasure
    infer_instance
  have hm := population_memLp_of_moment μ ν p₀ p₁ q h₀ h₁ hq A hfin
  have hs := measurableSet_populationSeedEvent (D := D) (measurableSet_activeSeeds A)
  have hp : populationMeasure μ ν (populationSeedEvent (activeSeeds A)) ≠ 0 := by
    rwa [populationSeedEvent_measure]
  have hcond : MemLp (fun z => A.output (populationInput p₀ p₁ q z)) 2
      (populationMeasure μ (cond ν (activeSeeds A))) := by
    rw [← populationMeasure_condition_seed]
    exact (hm.restrict (populationSeedEvent (activeSeeds A))).smul_measure (ENNReal.inv_ne_top.mpr hp)
  have hZ : MemLp (fun z => (activeProcedure ν A).output (populationInput p₀ p₁ q z)) 2
      (populationMeasure μ (cond ν (activeSeeds A))) :=
    (hcond.const_mul (ν.real (activeSeeds A))).add (memLp_const _)
  have hZfin : populationSecondMoment μ (cond ν (activeSeeds A)) p₀ p₁ q (activeProcedure ν A) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hZ.integrable_sq.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))).mpr hZ.integrable_sq
  have h := normalized_event_moment (populationMeasure μ ν) (populationSeedEvent (activeSeeds A))
    hs hp _ hm
  rw [populationMeasure_condition_seed,population_inactive_mean] at h
  have hreal : (populationMeasure μ ν).real (populationSeedEvent (activeSeeds A)) =
      ν.real (activeSeeds A) := by simp only [measureReal_def,populationSeedEvent_measure]
  rw [hreal] at h
  change (∫ z, ((activeProcedure ν A).output (populationInput p₀ p₁ q z))^2
      ∂populationMeasure μ (cond ν (activeSeeds A))) ≤ _ at h
  rw [population_second_moment_toReal μ (cond ν (activeSeeds A)) p₀ p₁ q h₀ h₁ hq
    (activeProcedure ν A) hZfin,population_second_moment_toReal μ ν p₀ p₁ q h₀ h₁ hq A hfin] at h
  have hh := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_toReal hZfin] at hh

theorem active_population_guarantee {R : Type} [MeasurableSpace R]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : ℝ → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ : ℝ))
    (hρ' : (ρ : ℝ) ≤ 1/4) (M : ℝ) (hM : 0 ≤ M)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ : ℝ) M) :
    ν (activeSeeds A) ≠ 0 ∧
    CappedPopulationGuarantee μ (cond ν (activeSeeds A)) p₀ p₁ (activeProcedure ν A)
      (ρ : ℝ) (ν.real (activeSeeds A)*M+2*(ρ : ℝ)^2) := by
  have hc₀ := cappedPrior_const μ (ρ : ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ : ℝ) ρ (by linarith) le_rfl
  have hb₀ : |populationMean μ ν p₀ p₁ (fun _ => 0) A| ≤ (ρ : ℝ)/64 := by
    simpa using hguar.bias _ hc₀
  have hbρ : |populationMean μ ν p₀ p₁ (fun _ => ρ) A-(ρ : ℝ)| ≤ (ρ : ℝ)/64 := by
    simpa using hguar.bias _ hcρ
  have hp := activation_positive_of_bias μ ν p₀ p₁ A ρ hρ hb₀ hbρ
  have hf (q : ℝ → unitInterval) (hq : CappedPrior μ (ρ : ℝ) q) :
      populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (hguar.moment q hq) ENNReal.ofReal_lt_top)
  refine ⟨hp,?_,?_,?_⟩
  · intro q hq
    apply (population_activation_moment μ ν p₀ p₁ q h₀ h₁ hq.1 A hp (hf q hq)).trans
    apply ENNReal.ofReal_le_ofReal
    have hMb : (populationSecondMoment μ ν p₀ p₁ q A).toReal ≤ M := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment q hq)
      rwa [ENNReal.toReal_ofReal hM] at h
    have hb := abs_le.mp (hguar.bias q hq)
    have hθ := hq.2.2
    have hθ₀ : 0 ≤ ∫ d,(q d : ℝ) ∂μ := integral_nonneg (fun d => (q d).property.1)
    have hu : populationMean μ ν p₀ p₁ q A ≤ 65*(ρ : ℝ)/64 := by linarith
    have hl : -(65*(ρ : ℝ)/64) ≤ populationMean μ ν p₀ p₁ q A := by linarith
    have hs := sq_le_sq' hl hu
    have hm := mul_le_mul_of_nonneg_left hMb (measureReal_nonneg (μ := ν) (s := activeSeeds A))
    nlinarith [sq_nonneg (ρ : ℝ)]
  · intro q hq
    rw [population_activation_work μ ν p₀ p₁ q h₀ h₁ hq.1 A hp]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp) (hguar.work q hq)
  · intro q hq
    rw [population_activation_mean μ ν p₀ p₁ q h₀ h₁ hq.1 A hp (hf q hq)]
    exact hguar.bias q hq

theorem capped_guarantee_moment_floor {R : Type} [MeasurableSpace R]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : ℝ → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ : ℝ))
    (hρ' : (ρ : ℝ) ≤ 1/4) (M : ℝ) (hM : 0 ≤ M)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ : ℝ) M) : 2*(ρ : ℝ)/3 ≤ M := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by unfold populationMeasure; infer_instance
  have hc₀ := cappedPrior_const μ (ρ : ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ : ℝ) ρ (by linarith) le_rfl
  have hf (q : ℝ → unitInterval) (hq : CappedPrior μ (ρ : ℝ) q) :
      populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (hguar.moment q hq) ENNReal.ofReal_lt_top)
  have hvar := population_variance_floor μ ν p₀ p₁ h₀ h₁ ρ hρ hρ' A
    (hf _ hc₀) (hf _ hcρ) (by simpa using hguar.bias _ hc₀) (by simpa using hguar.bias _ hcρ)
  have hl2 := population_memLp_of_moment μ ν p₀ p₁ (fun _ => ρ) h₀ h₁ measurable_const A (hf _ hcρ)
  have hv := variance_le_expectation_sq hl2.aestronglyMeasurable
  simp only [Pi.pow_apply] at hv
  rw [population_second_moment_toReal μ ν p₀ p₁ (fun _ => ρ) h₀ h₁ measurable_const A (hf _ hcρ)] at hv
  have hMb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  rw [ENNReal.toReal_ofReal hM] at hMb
  exact hvar.trans (hv.trans hMb)

end ThresholdHC.CriticalEntropy
