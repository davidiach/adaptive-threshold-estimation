import ThresholdHC.CriticalEntropy.CriticalRisk

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem measurable_selected {I R Ω X : Type} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace R]
    [MeasurableSpace Ω] [MeasurableSpace X]
    (f : I → R × Ω → X) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun z : (I × R) × Ω => f z.1.1 (z.1.2,z.2)) := by
  have h : Measurable (fun z : I × (R × Ω) => f z.1 z.2) :=
    measurable_from_prod_countable_right hf
  exact h.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

/-- The policy index is selected by the independent seed and remains visible
in the full observation. No latent population parameter enters this procedure. -/
def selectedProcedure {I R E : Type} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace R] [MeasurableSpace E]
    (A : I → StoppedProcedure R E) : StoppedProcedure (I × R) E where
  stop := fun z => (A z.1.1).stop (z.1.2,z.2)
  output := fun z => (A z.1.1).output (z.1.2,z.2)
  measurable_stop := measurable_selected _ (fun i => (A i).measurable_stop)
  measurable_output := measurable_selected _ (fun i => (A i).measurable_output)
  stopPrefix := fun n => {z | (z.1.2,z.2) ∈ (A z.1.1).stopPrefix n}
  measurable_stopPrefix := by
    classical
    intro n
    have h : Measurable (fun z : (I × R) × (Fin n → Bool) =>
        if (z.1.2,z.2) ∈ (A z.1.1).stopPrefix n then true else false) :=
      measurable_selected (fun i z => if z ∈ (A i).stopPrefix n then true else false)
        (fun i => Measurable.ite ((A i).measurable_stopPrefix n) measurable_const measurable_const)
    convert h (measurableSet_singleton true) using 1
    ext z
    simp
  stop_observable := fun n z => (A z.1.1).stop_observable n (z.1.2,z.2)
  outputPrefix := fun n z => (A z.1.1).outputPrefix n (z.1.2,z.2)
  measurable_outputPrefix := fun n => measurable_selected _ (fun i => (A i).measurable_outputPrefix n)
  output_observable := fun n z hn => (A z.1.1).output_observable n (z.1.2,z.2) hn

theorem selectedProcedure_capped {I R E : Type} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace R] [MeasurableSpace E]
    (A : I → StoppedProcedure R E) (m : ℕ) (hcap : ∀ i z, (A i).stop z ≤ m) :
    ∀ z, (selectedProcedure A).stop z ≤ m := fun z => hcap z.1.1 (z.1.2,z.2)

theorem selected_seed_lintegral {I R Ω : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace R] [MeasurableSpace Ω]
    (κ : Measure I) (ν : Measure R) [IsProbabilityMeasure ν]
    (η : Measure Ω) [IsProbabilityMeasure η]
    (f : (I × R) × Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂(κ.prod ν).prod η) =
      ∑ i, κ {i}*(∫⁻ z : R × Ω, f ((i,z.1),z.2) ∂ν.prod η) := by
  rw [lintegral_prod _ hf.aemeasurable]
  rw [lintegral_prod _ (hf.lintegral_prod_right' : Measurable (fun z : I × R => ∫⁻ x, f (z,x) ∂η)).aemeasurable]
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]
  congr 1
  exact (lintegral_prod (μ := ν) (ν := η) _
    ((hf.comp (by fun_prop : Measurable (fun z : R × Ω => ((i,z.1),z.2))))).aemeasurable).symm

theorem selected_expected_work {I R E : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace R] [MeasurableSpace E]
    (κ : Measure I) (ν : Measure R) [IsProbabilityMeasure ν]
    (A : I → StoppedProcedure R E) (p : unitInterval) :
    expectedStoppedProcedureWork (κ.prod ν) p (selectedProcedure A) =
      ∑ i, κ {i}*expectedStoppedProcedureWork ν p (A i) := by
  exact selected_seed_lintegral κ ν (Tier2.tapeMeasure p) _
    (measurable_stoppedProcedureWork (selectedProcedure A))

theorem population_selected_lintegral {D I R : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (f : I → R × (ℕ → Bool) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ z, (fun t : (I × R) × (ℕ → Bool) => f t.1.1 (t.1.2,t.2)) (populationInput p₀ p₁ q z)
      ∂populationMeasure μ (κ.prod ν)) =
      ∑ i, κ {i}*(∫⁻ z, f i (populationInput p₀ p₁ q z) ∂populationMeasure μ ν) := by
  let g : (I × R) × (ℕ → Bool) → ℝ≥0∞ := fun t => f t.1.1 (t.1.2,t.2)
  have hg : Measurable g := measurable_selected f hf
  change (∫⁻ z, g (populationInput p₀ p₁ q z) ∂populationMeasure μ (κ.prod ν)) = _
  unfold populationMeasure
  rw [population_lintegral μ (κ.prod ν) p₀ p₁ q h₀ h₁ hq g hg]
  have hi (p : unitInterval) :
      (∫⁻ z, g z ∂(κ.prod ν).prod (Tier2.tapeMeasure p)) =
      ∑ i, κ {i}*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure p)) :=
    selected_seed_lintegral κ ν (Tier2.tapeMeasure p) g hg
  simp_rw [hi]
  have hm (i : I) : Measurable (fun d =>
      ENNReal.ofReal (q d : ℝ)*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₁ d)))+
      ENNReal.ofReal (1-(q d : ℝ))*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₀ d)))) := by
    exact ((ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp hq)).mul
      ((measurable_seeded_lintegral ν (f i) (hf i)).comp h₁)).add
      ((ENNReal.measurable_ofReal.comp (measurable_const.sub (measurable_subtype_coe.comp hq))).mul
        ((measurable_seeded_lintegral ν (f i) (hf i)).comp h₀))
  have he (d : D) :
      ENNReal.ofReal (q d : ℝ)*(∑ i, κ {i}*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₁ d))))+
      ENNReal.ofReal (1-(q d : ℝ))*(∑ i, κ {i}*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₀ d)))) =
      ∑ i, κ {i}*(ENNReal.ofReal (q d : ℝ)*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₁ d)))+
        ENNReal.ofReal (1-(q d : ℝ))*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₀ d)))) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [he]
  have hterm (i : I) : Measurable (fun d => κ {i}*(
      ENNReal.ofReal (q d : ℝ)*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₁ d)))+
      ENNReal.ofReal (1-(q d : ℝ))*(∫⁻ z, f i z ∂ν.prod (Tier2.tapeMeasure (p₀ d))))) :=
    measurable_const.mul (hm i)
  rw [lintegral_finsetSum Finset.univ (fun i hi => hterm i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_const_mul _ (hm i),population_lintegral μ ν p₀ p₁ q h₀ h₁ hq (f i) (hf i)]

theorem selected_population_work {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : I → StoppedProcedure R E) :
    populationExpectedWork μ (κ.prod ν) p₀ p₁ q (selectedProcedure A) =
      ∑ i, κ {i}*populationExpectedWork μ ν p₀ p₁ q (A i) := by
  exact population_selected_lintegral μ κ ν p₀ p₁ q h₀ h₁ hq _
    (fun i => measurable_stoppedProcedureWork (A i))

theorem capped_statistic_lintegral {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) (m : ℕ) (f : Fin (m+1) × Fin (m+1) → ℝ≥0∞) :
    (∫⁻ i, f i ∂cappedStatisticLaw μ ν p₀ p₁ q A m) =
      ∫⁻ z, f (stoppedStatistic m (cappedTranscript A m (populationInput p₀ p₁ q z)).2)
        ∂populationMeasure μ ν := by
  have hf : Measurable f := measurable_of_countable f
  have hT : Measurable (fun z : R × CappedWord m => stoppedStatistic m z.2) :=
    (measurable_of_countable (stoppedStatistic m)).comp measurable_snd
  rw [cappedStatisticLaw,lintegral_map hf hT,cappedTranscriptLaw]
  have hfT : Measurable (fun z : R × CappedWord m => f (stoppedStatistic m z.2)) := hf.comp hT
  rw [lintegral_map hfT ((measurable_cappedTranscript A m).comp
    (measurable_populationInput p₀ p₁ q h₀ h₁ hq))]
  rfl

theorem selected_statistic_lintegral {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : I → StoppedProcedure R E) (m : ℕ) (f : Fin (m+1) × Fin (m+1) → ℝ≥0∞) :
    (∫⁻ j, f j ∂cappedStatisticLaw μ (κ.prod ν) p₀ p₁ q (selectedProcedure A) m) =
      ∑ i, κ {i}*(∫⁻ j, f j ∂cappedStatisticLaw μ ν p₀ p₁ q (A i) m) := by
  rw [capped_statistic_lintegral μ (κ.prod ν) p₀ p₁ q h₀ h₁ hq]
  let g (i : I) (z : R × (ℕ → Bool)) := f (stoppedStatistic m (cappedTranscript (A i) m z).2)
  have hg (i : I) : Measurable (g i) := (measurable_of_countable f).comp
    ((measurable_of_countable (stoppedStatistic m)).comp
      (measurable_snd.comp (measurable_cappedTranscript (A i) m)))
  change (∫⁻ z, (fun t : (I × R) × (ℕ → Bool) => g t.1.1 (t.1.2,t.2)) (populationInput p₀ p₁ q z)
    ∂populationMeasure μ (κ.prod ν)) = _
  rw [population_selected_lintegral μ κ ν p₀ p₁ q h₀ h₁ hq g hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [capped_statistic_lintegral μ ν p₀ p₁ q h₀ h₁ hq]

theorem selected_statistic_mass {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : I → StoppedProcedure R E) (m : ℕ) (j : Fin (m+1) × Fin (m+1)) :
    cappedStatisticLaw μ (κ.prod ν) p₀ p₁ q (selectedProcedure A) m {j} =
      ∑ i, κ {i}*cappedStatisticLaw μ ν p₀ p₁ q (A i) m {j} := by
  classical
  have h := selected_statistic_lintegral μ κ ν p₀ p₁ q h₀ h₁ hq A m
    (({j} : Set (Fin (m+1) × Fin (m+1))).indicator (fun _ => 1))
  simpa only [lintegral_indicator_fun_one (measurableSet_singleton j)] using h

theorem selected_statistic_real_mass {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : I → StoppedProcedure R E) (m : ℕ) (j : Fin (m+1) × Fin (m+1)) :
    (cappedStatisticLaw μ (κ.prod ν) p₀ p₁ q (selectedProcedure A) m).real {j} =
      ∑ i, κ.real {i}*(cappedStatisticLaw μ ν p₀ p₁ q (A i) m).real {j} := by
  have hfin (i : I) : cappedStatisticLaw μ ν p₀ p₁ q (A i) m {j} ≠ ∞ := by
    let : IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ q (A i) m) :=
      cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq (A i) m
    exact measure_ne_top _ _
  rw [measureReal_def,selected_statistic_mass μ κ ν p₀ p₁ q h₀ h₁ hq A m j,
    ENNReal.toReal_sum (fun i hi => ENNReal.mul_ne_top (measure_ne_top _ _) (hfin i))]
  simp only [ENNReal.toReal_mul,measureReal_def]

theorem real_affinity_common_density_mixture {I K : Type} [Fintype I] [Fintype K]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (p q : K → ℝ)
    (r : I → K → ℝ) (hr : ∀ i k, 0 ≤ r i k) :
    realFiniteAffinity (fun k => ∑ i, w i*(p k*r i k)) (fun k => ∑ i, w i*(q k*r i k)) =
      ∑ i, w i*realFiniteAffinity (fun k => p k*r i k) (fun k => q k*r i k) := by
  have hscale (x y a : ℝ) (ha : 0 ≤ a) : Real.sqrt ((x*a)*(y*a)) = a*Real.sqrt (x*y) := by
    rw [show (x*a)*(y*a) = a^2*(x*y) by ring,Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha]
  have hsum (x : K → ℝ) (k : K) : (∑ i, w i*(x k*r i k)) = x k*(∑ i, w i*r i k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  unfold realFiniteAffinity
  simp_rw [hsum,hscale _ _ _ (Finset.sum_nonneg (fun i hi => mul_nonneg (hw i) (hr i _))),
    hscale _ _ _ (hr _ _)]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intros
  ring

theorem selected_affinity_real {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : I → StoppedProcedure R E) (m : ℕ) (hcap : ∀ i z, (A i).stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    (hellingerAffinity (cappedTranscriptLaw μ (κ.prod ν) p₀ p₁ q (selectedProcedure A) m)
      (cappedTranscriptLaw μ (κ.prod ν) p₀ p₁ r (selectedProcedure A) m)).toReal =
      ∑ i, κ.real {i}*(hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (A i) m)
        (cappedTranscriptLaw μ ν p₀ p₁ r (A i) m)).toReal := by
  let ref (i : I) (j : Fin (m+1) × Fin (m+1)) :=
    ((stoppedReference ν (A i) m).map (fun z => stoppedStatistic m z.2)).real {j}
  let lq (j : Fin (m+1) × Fin (m+1)) := (populationWordLikelihood μ p₀ p₁ q j.1.val j.2.val).toReal
  let lr (j : Fin (m+1) × Fin (m+1)) := (populationWordLikelihood μ p₀ p₁ r j.1.val j.2.val).toReal
  have hcellq (i : I) (j : Fin (m+1) × Fin (m+1)) :
      (cappedStatisticLaw μ ν p₀ p₁ q (A i) m).real {j} = lq j*ref i j :=
    cappedStatisticLaw_real_mass μ ν p₀ p₁ q h₀ h₁ hq (A i) m (hcap i) j
  have hcellr (i : I) (j : Fin (m+1) × Fin (m+1)) :
      (cappedStatisticLaw μ ν p₀ p₁ r (A i) m).real {j} = lr j*ref i j :=
    cappedStatisticLaw_real_mass μ ν p₀ p₁ r h₀ h₁ hr (A i) m (hcap i) j
  have hcomponent (i : I) :
      (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (A i) m)
        (cappedTranscriptLaw μ ν p₀ p₁ r (A i) m)).toReal =
      realFiniteAffinity (fun j => lq j*ref i j) (fun j => lr j*ref i j) := by
    rw [capped_observation_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr (A i) m (hcap i) hp]
    simp_rw [hcellq,hcellr]
  rw [capped_observation_affinity_real μ (κ.prod ν) p₀ p₁ q r h₀ h₁ hq hr
    (selectedProcedure A) m (selectedProcedure_capped A m hcap) hp]
  simp_rw [selected_statistic_real_mass μ κ ν p₀ p₁ q h₀ h₁ hq A m,
    selected_statistic_real_mass μ κ ν p₀ p₁ r h₀ h₁ hr A m,hcellq,hcellr,hcomponent]
  exact real_affinity_common_density_mixture (fun i => κ.real {i}) (fun i => measureReal_nonneg)
    lq lr ref (fun i j => measureReal_nonneg)

theorem population_seed_map {D R S : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (f : S → R) (hf : Measurable f) :
    (populationMeasure μ ν).map (Prod.map id (Prod.map id (Prod.map f id))) =
      populationMeasure μ (ν.map f) := by
  unfold populationMeasure
  rw [← Measure.map_prod_map μ (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))
    measurable_id (measurable_id.prodMap (hf.prodMap measurable_id)),Measure.map_id,
    ← Measure.map_prod_map uniformUnitMeasure (ν.prod uniformTapeMeasure)
      measurable_id (hf.prodMap measurable_id),Measure.map_id,
    ← Measure.map_prod_map ν uniformTapeMeasure hf measurable_id,Measure.map_id]

theorem population_reseed_lintegral {D R S : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (f : S → R) (hf : Measurable f) (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (Prod.map f id (populationInput p₀ p₁ q z)) ∂populationMeasure μ ν) =
      ∫⁻ z, F (populationInput p₀ p₁ q z) ∂populationMeasure μ (ν.map f) := by
  rw [← population_seed_map μ ν f hf]
  have hFP : Measurable (fun z : D × (ℝ × (R × (ℕ → ℝ))) => F (populationInput p₀ p₁ q z)) :=
    hF.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  rw [lintegral_map hFP
    (measurable_id.prodMap (measurable_id.prodMap (hf.prodMap measurable_id)))]
  rfl

theorem population_reseed_work {D R S E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) (f : S → R) (hf : Measurable f) :
    populationExpectedWork μ ν p₀ p₁ q (reseedProcedure A f hf) =
      populationExpectedWork μ (ν.map f) p₀ p₁ q A :=
  population_reseed_lintegral μ ν p₀ p₁ q h₀ h₁ hq f hf _ (measurable_stoppedProcedureWork A)

theorem reseed_statistic_lintegral {D R S E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) (m : ℕ) (f : S → R) (hf : Measurable f)
    (g : Fin (m+1) × Fin (m+1) → ℝ≥0∞) :
    (∫⁻ j, g j ∂cappedStatisticLaw μ ν p₀ p₁ q (reseedProcedure A f hf) m) =
      ∫⁻ j, g j ∂cappedStatisticLaw μ (ν.map f) p₀ p₁ q A m := by
  rw [capped_statistic_lintegral μ ν p₀ p₁ q h₀ h₁ hq,
    capped_statistic_lintegral μ (ν.map f) p₀ p₁ q h₀ h₁ hq]
  let F (z : R × (ℕ → Bool)) := g (stoppedStatistic m (cappedTranscript A m z).2)
  have hF : Measurable F := (measurable_of_countable g).comp
    ((measurable_of_countable (stoppedStatistic m)).comp (measurable_snd.comp (measurable_cappedTranscript A m)))
  exact population_reseed_lintegral μ ν p₀ p₁ q h₀ h₁ hq f hf F hF

end ThresholdHC.CriticalEntropy
