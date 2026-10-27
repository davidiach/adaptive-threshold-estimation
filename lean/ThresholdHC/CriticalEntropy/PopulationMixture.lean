import ThresholdHC.CriticalEntropy.UniformCoin

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.CriticalEntropy

theorem mixtureParameter_map {D : Type} (p₀ p₁ q : D → unitInterval) (d : D) :
    uniformUnitMeasure.map (fun u => mixtureParameter p₀ p₁ q (d,u)) =
      bernoulliMeasure (p₁ d) (p₀ d) (q d) := by
  let g : Bool → unitInterval := fun b => if b then p₁ d else p₀ d
  have hg : Measurable g := measurable_of_countable g
  have hf : (fun u => mixtureParameter p₀ p₁ q (d,u)) = g ∘ uniformCoinFlip (q d) := by
    funext u
    by_cases hu : u < (q d : ℝ) <;> simp [mixtureParameter, uniformCoinFlip, g, hu]
  have hm : Measurable (uniformCoinFlip (q d)) :=
    measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_id)
  rw [hf, ← Measure.map_map hg hm, uniformCoinFlip_map, map_bernoulliMeasure' true false hg (q d)]
  simp [g]

theorem lintegral_bernoulli_parameter (p p₀ p₁ : unitInterval)
    (F : unitInterval → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂bernoulliMeasure p₁ p₀ p) =
      ENNReal.ofReal (p : ℝ)*F p₁ + ENNReal.ofReal (1-(p : ℝ))*F p₀ := by
  simp [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac' _ hF, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_nnreal_eq]

theorem mixtureParameter_lintegral {D : Type} (p₀ p₁ q : D → unitInterval) (d : D)
    (F : unitInterval → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u, F (mixtureParameter p₀ p₁ q (d,u)) ∂uniformUnitMeasure) =
      ENNReal.ofReal (q d : ℝ)*F (p₁ d) + ENNReal.ofReal (1-(q d : ℝ))*F (p₀ d) := by
  have hm : Measurable (fun u => mixtureParameter p₀ p₁ q (d,u)) := by
    change Measurable (fun u : ℝ => if u < (q d : ℝ) then p₁ d else p₀ d)
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  rw [← lintegral_map hF hm, mixtureParameter_map, lintegral_bernoulli_parameter _ _ _ F hF]

theorem population_lintegral {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (populationInput p₀ p₁ q z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) =
    ∫⁻ d, ENNReal.ofReal (q d : ℝ)*(∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d))) +
      ENNReal.ofReal (1-(q d : ℝ))*(∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d))) ∂μ := by
  have hm : Measurable (fun z : D × (ℝ × (R × (ℕ → ℝ))) =>
      F (populationInput p₀ p₁ q z)) :=
    hF.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq (R := R))
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro d
  have hd : Measurable (fun z : ℝ × (R × (ℕ → ℝ)) =>
      F (populationInput p₀ p₁ q (d,z))) := hm.comp measurable_prodMk_left
  rw [lintegral_prod _ hd.aemeasurable]
  have he (u : ℝ) :
      (∫⁻ z, F (populationInput p₀ p₁ q (d,(u,z))) ∂ν.prod uniformTapeMeasure) =
        ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (mixtureParameter p₀ p₁ q (d,u))) :=
    (seeded_lintegral_uniform ν (mixtureParameter p₀ p₁ q (d,u)) F hF).symm
  simp_rw [he]
  exact mixtureParameter_lintegral p₀ p₁ q d _ (measurable_seeded_lintegral ν F hF)

theorem population_lintegral_const {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (populationInput p₀ p₁ (fun _ => c) z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) =
    ENNReal.ofReal (c : ℝ)*(∫⁻ d, ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d)) ∂μ) +
      ENNReal.ofReal (1-(c : ℝ))*(∫⁻ d, ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d)) ∂μ) := by
  rw [population_lintegral μ ν p₀ p₁ _ h₀ h₁ measurable_const F hF]
  have hm₀ : Measurable (fun d => ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d))) :=
    (measurable_seeded_lintegral ν F hF).comp h₀
  have hm₁ : Measurable (fun d => ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d))) :=
    (measurable_seeded_lintegral ν F hF).comp h₁
  have hmul : Measurable (fun d => ENNReal.ofReal (c : ℝ)*
      (∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d)))) := measurable_const.mul hm₁
  rw [lintegral_add_left hmul,
    lintegral_const_mul _ hm₁, lintegral_const_mul _ hm₀]

/-- Finite population expectations at the null law and at one positive constant
prior force finite integrated expectations under each sign. -/
theorem population_finite_components {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ))
    (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F)
    (hnull : (∫⁻ z, F (populationInput p₀ p₁ (fun _ => 0) z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) ≠ ∞)
    (hmix : (∫⁻ z, F (populationInput p₀ p₁ (fun _ => c) z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) ≠ ∞) :
    (∫⁻ d, ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d)) ∂μ) ≠ ∞ ∧
    (∫⁻ d, ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d)) ∂μ) ≠ ∞ := by
  rw [population_lintegral_const μ ν p₀ p₁ h₀ h₁ 0 F hF] at hnull
  norm_num at hnull
  refine ⟨hnull, ?_⟩
  rw [population_lintegral_const μ ν p₀ p₁ h₀ h₁ c F hF] at hmix
  intro htop
  have hc' : ENNReal.ofReal (c : ℝ) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  simp [htop, hc'] at hmix

theorem population_ae_finite_components {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ))
    (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F)
    (hnull : (∫⁻ z, F (populationInput p₀ p₁ (fun _ => 0) z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) ≠ ∞)
    (hmix : (∫⁻ z, F (populationInput p₀ p₁ (fun _ => c) z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) ≠ ∞) :
    ∀ᵐ d ∂μ, (∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d))) ≠ ∞ ∧
      (∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d))) ≠ ∞ := by
  obtain ⟨hfin₀,hfin₁⟩ := population_finite_components μ ν p₀ p₁ h₀ h₁ c hc F hF hnull hmix
  have ha₀ := ae_lt_top ((measurable_seeded_lintegral ν F hF).comp h₀) hfin₀
  have ha₁ := ae_lt_top ((measurable_seeded_lintegral ν F hF).comp h₁) hfin₁
  filter_upwards [ha₀,ha₁] with d hd₀ hd₁ using ⟨hd₀.ne,hd₁.ne⟩

theorem mixtureParameter_integral {D : Type} (p₀ p₁ q : D → unitInterval) (d : D)
    (F : unitInterval → ℝ) (hF : Measurable F) :
    (∫ u, F (mixtureParameter p₀ p₁ q (d,u)) ∂uniformUnitMeasure) =
      (q d : ℝ)*F (p₁ d) + (1-(q d : ℝ))*F (p₀ d) := by
  have hm : Measurable (fun u => mixtureParameter p₀ p₁ q (d,u)) := by
    change Measurable (fun u : ℝ => if u < (q d : ℝ) then p₁ d else p₀ d)
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable, mixtureParameter_map,
    integral_bernoulliMeasure]
  simp only [smul_eq_mul]

/-- Signed expectations are decomposed only under actual population
integrability. Nonnegative expectations above require no finiteness. -/
theorem population_integral {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (F : R × (ℕ → Bool) → ℝ) (hF : Measurable F)
    (hint : Integrable (fun z => F (populationInput p₀ p₁ q z))
      (μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure)))) :
    (∫ z, F (populationInput p₀ p₁ q z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) =
    ∫ d, (q d : ℝ)*(∫ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d))) +
      (1-(q d : ℝ))*(∫ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d))) ∂μ := by
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [hint.prod_right_ae] with d hd
  rw [integral_prod _ hd]
  have he (u : ℝ) :
      (∫ z, F (populationInput p₀ p₁ q (d,(u,z))) ∂ν.prod uniformTapeMeasure) =
        ∫ z, F z ∂ν.prod (Tier2.tapeMeasure (mixtureParameter p₀ p₁ q (d,u))) := by
    rw [← seeded_uniformCoinTape_map ν (mixtureParameter p₀ p₁ q (d,u))]
    symm
    exact integral_map
      (measurable_id.prodMap (measurable_uniformCoinTape.comp
        (measurable_const.prodMk measurable_id))).aemeasurable hF.aestronglyMeasurable
  simp_rw [he]
  exact mixtureParameter_integral p₀ p₁ q d _ (measurable_seeded_integral ν F hF)

theorem population_finite_all {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ))
    (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F)
    (hnull : (∫⁻ z, F (populationInput p₀ p₁ (fun _ => 0) z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) ≠ ∞)
    (hmix : (∫⁻ z, F (populationInput p₀ p₁ (fun _ => c) z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) ≠ ∞)
    (q : D → unitInterval) (hq : Measurable q) :
    (∫⁻ z, F (populationInput p₀ p₁ q z)
      ∂μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))) ≠ ∞ := by
  obtain ⟨hf₀,hf₁⟩ := population_finite_components μ ν p₀ p₁ h₀ h₁ c hc F hF hnull hmix
  rw [population_lintegral μ ν p₀ p₁ q h₀ h₁ hq F hF]
  have hm₁ : Measurable (fun d => ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d))) :=
    (measurable_seeded_lintegral ν F hF).comp h₁
  have hb : (∫⁻ d, ENNReal.ofReal (q d : ℝ)*(∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d))) +
      ENNReal.ofReal (1-(q d : ℝ))*(∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d))) ∂μ) ≤
      (∫⁻ d, ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d)) ∂μ) +
      (∫⁻ d, ∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d)) ∂μ) := by
    rw [← lintegral_add_left hm₁]
    apply lintegral_mono
    intro d
    have hp : ENNReal.ofReal (q d : ℝ) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal (q d).property.2
    have hn : ENNReal.ofReal (1-(q d : ℝ)) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal (sub_le_self (1 : ℝ) (q d).property.1)
    apply add_le_add
    · calc
        _ ≤ 1 * (∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₁ d))) := mul_le_mul' hp le_rfl
        _ = _ := one_mul _
    · calc
        _ ≤ 1 * (∫⁻ z, F z ∂ν.prod (Tier2.tapeMeasure (p₀ d))) := mul_le_mul' hn le_rfl
        _ = _ := one_mul _
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf₁,hf₀⟩) hb

/-- A single common full-measure set supplies finite work and square-integrable
output under both signs; neither property is assumed pointwise in the gap. -/
theorem population_conditional_finiteness {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (hw₀ : populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hw₁ : populationExpectedWork μ ν p₀ p₁ (fun _ => c) A ≠ ∞) :
    (∀ᵐ d ∂μ,
      MemLp id 2 ((ν.prod (Tier2.tapeMeasure (p₀ d))).map A.output) ∧
      MemLp id 2 ((ν.prod (Tier2.tapeMeasure (p₁ d))).map A.output) ∧
      expectedStoppedProcedureWork ν (p₀ d) A ≠ ∞ ∧
      expectedStoppedProcedureWork ν (p₁ d) A ≠ ∞) ∧
    Integrable (fun d => conditionalMean ν (p₀ d) A) μ ∧
    Integrable (fun d => conditionalMean ν (p₁ d) A) μ := by
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  have hm := population_ae_finite_components μ ν p₀ p₁ h₀ h₁ c hc _ hsq hm₀ hm₁
  have hw := population_ae_finite_components μ ν p₀ p₁ h₀ h₁ c hc _
    (measurable_stoppedProcedureWork A) hw₀ hw₁
  have hi := population_finite_components μ ν p₀ p₁ h₀ h₁ c hc _ hsq hm₀ hm₁
  refine ⟨?_, conditionalMean_integrable_of_moment μ ν p₀ h₀ A hi.1,
    conditionalMean_integrable_of_moment μ ν p₁ h₁ A hi.2⟩
  filter_upwards [hm,hw] with d hdm hdw
  exact ⟨(conditionalSecondMoment_finite_iff ν (p₀ d) A).mp hdm.1,
    (conditionalSecondMoment_finite_iff ν (p₁ d) A).mp hdm.2,hdw.1,hdw.2⟩

theorem population_second_moment_formula {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R ℝ) :
    populationSecondMoment μ ν p₀ p₁ q A =
      ∫⁻ d, ENNReal.ofReal (q d : ℝ)*conditionalSecondMoment ν (p₁ d) A +
        ENNReal.ofReal (1-(q d : ℝ))*conditionalSecondMoment ν (p₀ d) A ∂μ :=
  population_lintegral μ ν p₀ p₁ q h₀ h₁ hq _
    (ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2))

theorem population_work_formula {D R E : Type} [MeasurableSpace D] [MeasurableSpace R]
    [MeasurableSpace E] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) :
    populationExpectedWork μ ν p₀ p₁ q A =
      ∫⁻ d, ENNReal.ofReal (q d : ℝ)*expectedStoppedProcedureWork ν (p₁ d) A +
        ENNReal.ofReal (1-(q d : ℝ))*expectedStoppedProcedureWork ν (p₀ d) A ∂μ :=
  population_lintegral μ ν p₀ p₁ q h₀ h₁ hq _ (measurable_stoppedProcedureWork A)

theorem population_mean_formula {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R ℝ)
    (hfin : populationSecondMoment μ ν p₀ p₁ q A ≠ ∞) :
    populationMean μ ν p₀ p₁ q A =
      ∫ d, (q d : ℝ)*conditionalMean ν (p₁ d) A +
        (1-(q d : ℝ))*conditionalMean ν (p₀ d) A ∂μ := by
  have hm : Measurable (fun z => A.output (populationInput p₀ p₁ q z)) :=
    A.measurable_output.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  have hs : Integrable (fun z => (A.output (populationInput p₀ p₁ q z))^2)
      (populationMeasure μ ν) :=
    (lintegral_ofReal_ne_top_iff_integrable (hm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))).mp hfin
  have hL2 := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hs
  have hi : Integrable (fun z => A.output (populationInput p₀ p₁ q z))
      (populationMeasure μ ν) := by
    let : IsProbabilityMeasure (populationMeasure μ ν) := by
      unfold populationMeasure; infer_instance
    exact hL2.integrable (by norm_num)
  exact population_integral μ ν p₀ p₁ q A.output A.measurable_output hi

/-- Two finite population laws also ensure finite moment and work at every
measurable sign prior. No common numerical bound across priors is claimed. -/
theorem population_finiteness_transfer {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc : 0 < (c : ℝ)) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (hw₀ : populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hw₁ : populationExpectedWork μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (q : D → unitInterval) (hq : Measurable q) :
    populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ ∧
      populationExpectedWork μ ν p₀ p₁ q A ≠ ∞ :=
  ⟨population_finite_all μ ν p₀ p₁ h₀ h₁ c hc _
      (ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)) hm₀ hm₁ q hq,
    population_finite_all μ ν p₀ p₁ h₀ h₁ c hc _
      (measurable_stoppedProcedureWork A) hw₀ hw₁ q hq⟩

end ThresholdHC.CriticalEntropy
