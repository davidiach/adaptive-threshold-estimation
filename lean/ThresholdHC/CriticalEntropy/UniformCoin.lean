import ThresholdHC.CriticalEntropy.PopulationModel

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.CriticalEntropy

theorem uniformCoinFlip_true (p : unitInterval) :
    uniformUnitMeasure {u | uniformCoinFlip p u = true} = ENNReal.ofReal (p : ℝ) := by
  have hs : {u | uniformCoinFlip p u = true} = Set.Iio (p : ℝ) := by
    ext u; simp [uniformCoinFlip]
  rw [hs, uniformUnitMeasure, Measure.restrict_apply measurableSet_Iio]
  have he : Set.Iio (p : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 (p : ℝ) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨hu,h0,_⟩; exact ⟨h0,hu⟩
    · rintro ⟨h0,hu⟩; exact ⟨hu,h0,hu.le.trans p.property.2⟩
  rw [he]
  simp

theorem uniformCoinFlip_map (p : unitInterval) :
    uniformUnitMeasure.map (uniformCoinFlip p) = bernoulliMeasure true false p := by
  apply Measure.ext_of_singleton
  intro b
  have hm : Measurable (uniformCoinFlip p) :=
    measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_id)
  cases b with
  | true =>
    rw [Measure.map_apply hm (measurableSet_singleton true)]
    change uniformUnitMeasure {u | uniformCoinFlip p u = true} = _
    rw [uniformCoinFlip_true]
    simp [bernoulliMeasure_def]
    change ENNReal.ofReal ((unitInterval.toNNReal p : ℝ≥0) : ℝ) =
      ((unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞)
    simp only [ENNReal.ofReal_coe_nnreal]
  | false =>
    have hc : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_singleton true),
      prob_compl_eq_one_sub (measurableSet_singleton true)]
    congr 1
    rw [Measure.map_apply hm (measurableSet_singleton true)]
    change uniformUnitMeasure {u | uniformCoinFlip p u = true} = _
    rw [uniformCoinFlip_true]
    simp [bernoulliMeasure_def]
    change ENNReal.ofReal ((unitInterval.toNNReal p : ℝ≥0) : ℝ) =
      ((unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞)
    simp only [ENNReal.ofReal_coe_nnreal]

theorem uniformCoinTape_map (p : unitInterval) :
    uniformTapeMeasure.map (uniformCoinTape p) = Tier2.tapeMeasure p := by
  have hm : Measurable (uniformCoinFlip p) :=
    measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_id)
  unfold uniformTapeMeasure uniformCoinTape Tier2.tapeMeasure
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => uniformUnitMeasure) (fun _ => hm)]
  simp_rw [uniformCoinFlip_map]

theorem seeded_uniformCoinTape_map {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) :
    (ν.prod uniformTapeMeasure).map (fun z => (z.1,uniformCoinTape p z.2)) =
      ν.prod (Tier2.tapeMeasure p) := by
  have hm : Measurable (uniformCoinTape p) :=
    measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
  change (ν.prod uniformTapeMeasure).map (Prod.map id (uniformCoinTape p)) = _
  rw [← Measure.map_prod_map ν uniformTapeMeasure measurable_id hm,
    Measure.map_id, uniformCoinTape_map]

theorem conditionalSecondMoment_uniform {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R ℝ) :
    conditionalSecondMoment ν p A =
      ∫⁻ z, ENNReal.ofReal ((A.output (uniformProcedureState (p,z)))^2)
        ∂ν.prod uniformTapeMeasure := by
  unfold conditionalSecondMoment
  rw [← seeded_uniformCoinTape_map ν p]
  exact lintegral_map (ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2))
    (measurable_id.prodMap (measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)))

theorem conditionalMean_uniform {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R ℝ) :
    conditionalMean ν p A =
      ∫ z, A.output (uniformProcedureState (p,z)) ∂ν.prod uniformTapeMeasure := by
  unfold conditionalMean
  rw [← seeded_uniformCoinTape_map ν p]
  exact integral_map
    (measurable_id.prodMap (measurable_uniformCoinTape.comp
      (measurable_const.prodMk measurable_id))).aemeasurable
    A.measurable_output.aestronglyMeasurable

theorem conditionalWork_uniform {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R E) :
    expectedStoppedProcedureWork ν p A =
      ∫⁻ z, stoppedProcedureWork A (uniformProcedureState (p,z)) ∂ν.prod uniformTapeMeasure := by
  unfold expectedStoppedProcedureWork
  rw [← seeded_uniformCoinTape_map ν p]
  exact lintegral_map (measurable_stoppedProcedureWork A)
    (measurable_id.prodMap (measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)))

theorem measurable_conditionalSecondMoment {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ) :
    Measurable (fun p => conditionalSecondMoment ν p A) := by
  have hm : Measurable (fun z : unitInterval × (R × (ℕ → ℝ)) =>
      ENNReal.ofReal ((A.output (uniformProcedureState z))^2)) :=
    ENNReal.measurable_ofReal.comp
      ((A.measurable_output.comp measurable_uniformProcedureState).pow_const 2)
  have hi : Measurable (fun p : unitInterval =>
      ∫⁻ z, ENNReal.ofReal ((A.output (uniformProcedureState (p,z)))^2)
        ∂ν.prod uniformTapeMeasure) := hm.lintegral_prod_right'
  convert hi using 1
  funext p
  exact conditionalSecondMoment_uniform ν p A

theorem measurable_conditionalMean {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ) :
    Measurable (fun p => conditionalMean ν p A) := by
  have hm : StronglyMeasurable (fun z : unitInterval × (R × (ℕ → ℝ)) =>
      A.output (uniformProcedureState z)) :=
    (A.measurable_output.comp measurable_uniformProcedureState).stronglyMeasurable
  have hi : Measurable (fun p : unitInterval =>
      ∫ z, A.output (uniformProcedureState (p,z)) ∂ν.prod uniformTapeMeasure) :=
    hm.integral_prod_right'.measurable
  convert hi using 1
  funext p
  exact conditionalMean_uniform ν p A

theorem measurable_conditionalWork {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) :
    Measurable (fun p => expectedStoppedProcedureWork ν p A) := by
  have hm : Measurable (fun z : unitInterval × (R × (ℕ → ℝ)) =>
      stoppedProcedureWork A (uniformProcedureState z)) :=
    (measurable_stoppedProcedureWork A).comp measurable_uniformProcedureState
  have hi : Measurable (fun p : unitInterval =>
      ∫⁻ z, stoppedProcedureWork A (uniformProcedureState (p,z)) ∂ν.prod uniformTapeMeasure) :=
    hm.lintegral_prod_right'
  convert hi using 1
  funext p
  exact conditionalWork_uniform ν p A

theorem conditionalSecondMoment_finite_iff {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ) :
    conditionalSecondMoment ν p A ≠ ∞ ↔
      MemLp id 2 ((ν.prod (Tier2.tapeMeasure p)).map A.output) := by
  calc
    _ ↔ Integrable (fun z => (A.output z)^2) (ν.prod (Tier2.tapeMeasure p)) :=
      lintegral_ofReal_ne_top_iff_integrable (A.measurable_output.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => sq_nonneg (A.output z)))
    _ ↔ MemLp A.output 2 (ν.prod (Tier2.tapeMeasure p)) :=
      (memLp_two_iff_integrable_sq A.measurable_output.aestronglyMeasurable).symm
    _ ↔ _ := (memLp_map_measure_iff (f := A.output) (g := id)
      measurable_id.aestronglyMeasurable A.measurable_output.aemeasurable).symm

theorem conditionalMean_output_law {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ) :
    (∫ x : ℝ, x ∂(ν.prod (Tier2.tapeMeasure p)).map A.output) = conditionalMean ν p A :=
  integral_map A.measurable_output.aemeasurable measurable_id.aestronglyMeasurable

theorem conditionalSecondMoment_output_law {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ)
    (hfinite : conditionalSecondMoment ν p A ≠ ∞) :
    (∫ x : ℝ, x^2 ∂(ν.prod (Tier2.tapeMeasure p)).map A.output) =
      (conditionalSecondMoment ν p A).toReal := by
  have hm := (conditionalSecondMoment_finite_iff ν p A).mp hfinite
  have hi : Integrable (fun z => (A.output z)^2) (ν.prod (Tier2.tapeMeasure p)) := by
    have hA : MemLp A.output 2 (ν.prod (Tier2.tapeMeasure p)) :=
      (memLp_map_measure_iff (f := A.output) (g := id)
        measurable_id.aestronglyMeasurable A.measurable_output.aemeasurable).mp hm
    exact hA.integrable_sq
  have hsq : Measurable (fun x : ℝ => x^2) := by fun_prop
  rw [integral_map A.measurable_output.aemeasurable hsq.aestronglyMeasurable]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => sq_nonneg (A.output z)))
    hi.aestronglyMeasurable

theorem seeded_lintegral_uniform {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure p)) =
      ∫⁻ z, F (uniformProcedureState (p,z)) ∂ν.prod uniformTapeMeasure := by
  rw [← seeded_uniformCoinTape_map ν p]
  exact lintegral_map hF (measurable_id.prodMap
    (measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)))

theorem measurable_seeded_lintegral {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun p : unitInterval => ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure p)) := by
  have hm : Measurable (fun z : unitInterval × (R × (ℕ → ℝ)) =>
      F (uniformProcedureState z)) := hF.comp measurable_uniformProcedureState
  have hi : Measurable (fun p : unitInterval =>
      ∫⁻ z, F (uniformProcedureState (p,z)) ∂ν.prod uniformTapeMeasure) :=
    hm.lintegral_prod_right'
  convert hi using 1
  funext p
  exact seeded_lintegral_uniform ν p F hF

theorem measurable_seeded_integral {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (F : R × (ℕ → Bool) → ℝ) (hF : Measurable F) :
    Measurable (fun p : unitInterval => ∫ z, F z ∂ν.prod (Tier2.tapeMeasure p)) := by
  have hm : StronglyMeasurable (fun z : unitInterval × (R × (ℕ → ℝ)) =>
      F (uniformProcedureState z)) := (hF.comp measurable_uniformProcedureState).stronglyMeasurable
  have hi : Measurable (fun p : unitInterval =>
      ∫ z, F (uniformProcedureState (p,z)) ∂ν.prod uniformTapeMeasure) :=
    hm.integral_prod_right'.measurable
  convert hi using 1
  funext p
  rw [← seeded_uniformCoinTape_map ν p]
  exact integral_map
    (measurable_id.prodMap (measurable_uniformCoinTape.comp
      (measurable_const.prodMk measurable_id))).aemeasurable hF.aestronglyMeasurable

theorem conditionalMean_integrable_of_moment {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p : D → unitInterval) (hp : Measurable p) (A : StoppedProcedure R ℝ)
    (hfin : (∫⁻ d, conditionalSecondMoment ν (p d) A ∂μ) ≠ ∞) :
    Integrable (fun d => conditionalMean ν (p d) A) μ := by
  let Y : D × (R × (ℕ → ℝ)) → ℝ :=
    fun z => A.output (uniformProcedureState (p z.1,z.2))
  have hY : Measurable Y := A.measurable_output.comp
    (measurable_uniformProcedureState.comp ((hp.comp measurable_fst).prodMk measurable_snd))
  have hm : Measurable (fun z => ENNReal.ofReal ((Y z)^2)) :=
    ENNReal.measurable_ofReal.comp (hY.pow_const 2)
  have he : (∫⁻ z, ENNReal.ofReal ((Y z)^2) ∂μ.prod (ν.prod uniformTapeMeasure)) =
      ∫⁻ d, conditionalSecondMoment ν (p d) A ∂μ := by
    rw [lintegral_prod _ hm.aemeasurable]
    apply lintegral_congr
    intro d
    exact (conditionalSecondMoment_uniform ν (p d) A).symm
  have hsq : Integrable (fun z => (Y z)^2) (μ.prod (ν.prod uniformTapeMeasure)) :=
    (lintegral_ofReal_ne_top_iff_integrable (hY.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => sq_nonneg (Y z)))).mp (he ▸ hfin)
  have hL2 : MemLp Y 2 (μ.prod (ν.prod uniformTapeMeasure)) :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mpr hsq
  have hi : Integrable Y (μ.prod (ν.prod uniformTapeMeasure)) := hL2.integrable (by norm_num)
  have hmean := hi.integral_prod_left
  simpa only [Y, ← conditionalMean_uniform] using hmean

end ThresholdHC.CriticalEntropy
