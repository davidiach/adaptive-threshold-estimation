import ThresholdHC.CriticalEntropy.ObservationModel
import ThresholdHC.CriticalEntropy.StoppedTape
import ThresholdHC.CriticalEntropy.PopulationMixture

/-!
Exact finite-word and head-count probabilities for the actual population
experiment, with arbitrary measurable seeds and observable stopping.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem streamProb_heads (p : ℝ) {n : ℕ} (x : Fin n → Bool) :
    streamProb p x = p ^ wordHeads x * (1-p) ^ (n-wordHeads x) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have ht : (Finset.univ.filter (fun i : Fin n => ¬x i = true)).card =
      n-wordHeads x := by unfold wordHeads; omega
  simp only [streamProb, Finset.prod_ite, Finset.prod_const]
  rw [ht]
  rfl

theorem measurableSet_stoppedSeedCell {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E] (A : StoppedProcedure R E)
    {n : ℕ} (x : Fin n → Bool) (S : Set R) (hS : MeasurableSet S) :
    MeasurableSet (stoppedSeedCell A x S) :=
  hS.inter ((measurable_id.prodMk measurable_const) (A.measurable_stopPrefix n))

theorem stopped_word_probability {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) {n : ℕ} (x : Fin n → Bool)
    (S : Set R) (hS : MeasurableSet S) :
    (ν.prod (Tier2.tapeMeasure p))
      {z | z.1 ∈ S ∧ A.stop z = n ∧ Tier2.tapePrefix n z.2 = x} =
      ν (stoppedSeedCell A x S) *
        ENNReal.ofReal ((p : ℝ)^wordHeads x*(1-(p : ℝ))^(n-wordHeads x)) := by
  have hcell := measurableSet_stoppedSeedCell A x S hS
  have hm := congrArg (fun μ => μ (stoppedSeedCell A x S ×ˢ {x}))
    (seeded_tape_prefix_map ν p n)
  rw [Measure.map_apply (measurable_id.prodMap (Tier2.measurable_prefix n))
    (hcell.prod (measurableSet_singleton x)), Measure.prod_prod] at hm
  have he : {z : R × (ℕ → Bool) | z.1 ∈ S ∧ A.stop z = n ∧ Tier2.tapePrefix n z.2 = x} =
      Prod.map id (Tier2.tapePrefix n) ⁻¹' (stoppedSeedCell A x S ×ˢ {x}) := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_prod, Prod.map_fst, id_eq,
      Prod.map_snd, mem_singleton_iff, stoppedSeedCell]
    constructor
    · rintro ⟨hs, hn, hx⟩
      refine ⟨⟨hs, ?_⟩, hx⟩
      rw [← hx]
      exact (A.stop_observable n z).2 hn
    · rintro ⟨⟨hs, hn⟩, hx⟩
      refine ⟨hs, ?_, hx⟩
      apply (A.stop_observable n z).1
      rwa [hx]
  rw [he, hm]
  congr 1
  rw [← streamProb_heads, ← Tier2.finiteMeasure_real_singleton, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem population_event_probability {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (S : Set (R × (ℕ → Bool))) (hS : MeasurableSet S) :
    (populationMeasure μ ν) (populationInput p₀ p₁ q ⁻¹' S) =
      ∫⁻ d, ENNReal.ofReal (q d : ℝ)*(ν.prod (Tier2.tapeMeasure (p₁ d))) S +
        ENNReal.ofReal (1-(q d : ℝ))*(ν.prod (Tier2.tapeMeasure (p₀ d))) S ∂μ := by
  have hi : Measurable (S.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hS
  have h := population_lintegral μ ν p₀ p₁ q h₀ h₁ hq _ hi
  have he : (fun z => S.indicator (fun _ => (1 : ℝ≥0∞)) (populationInput p₀ p₁ q z)) =
      (populationInput p₀ p₁ q ⁻¹' S).indicator (fun _ => 1) := by
    funext z
    by_cases hz : populationInput p₀ p₁ q z ∈ S <;> simp [hz]
  rw [he, lintegral_indicator_fun_one ((measurable_populationInput p₀ p₁ q h₀ h₁ hq) hS)] at h
  simp_rw [lintegral_indicator_fun_one hS] at h
  exact h

theorem measurable_wordLikelihood (n k : ℕ) : Measurable (fun p => wordLikelihood p n k) := by
  unfold wordLikelihood
  fun_prop

theorem population_stopped_word_probability {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) {n : ℕ} (x : Fin n → Bool)
    (S : Set R) (hS : MeasurableSet S) :
    (populationMeasure μ ν) (populationInput p₀ p₁ q ⁻¹'
      {z | z.1 ∈ S ∧ A.stop z = n ∧ Tier2.tapePrefix n z.2 = x}) =
      ν (stoppedSeedCell A x S) * populationWordLikelihood μ p₀ p₁ q n (wordHeads x) := by
  have hs : MeasurableSet {z : R × (ℕ → Bool) |
      z.1 ∈ S ∧ A.stop z = n ∧ Tier2.tapePrefix n z.2 = x} :=
    (measurable_fst hS).inter ((A.measurable_stop (measurableSet_singleton (n : ℕ∞))).inter
      (((Tier2.measurable_prefix n).comp measurable_snd) (measurableSet_singleton x)))
  rw [population_event_probability μ ν p₀ p₁ q h₀ h₁ hq _ hs]
  simp_rw [stopped_word_probability ν _ A x S hS]
  unfold populationWordLikelihood
  have hm : Measurable (fun d => ENNReal.ofReal (q d : ℝ)*wordLikelihood (p₁ d) n (wordHeads x) +
      ENNReal.ofReal (1-(q d : ℝ))*wordLikelihood (p₀ d) n (wordHeads x)) := by
    unfold wordLikelihood
    fun_prop
  rw [← lintegral_const_mul _ hm]
  apply lintegral_congr
  intro d
  unfold wordLikelihood
  ring

theorem population_stopped_heads_probability {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (n k : ℕ)
    (S : (Fin n → Bool) → Set R) (hS : ∀ x, MeasurableSet (S x)) :
    (populationMeasure μ ν) (populationInput p₀ p₁ q ⁻¹'
      {z | A.stop z = n ∧ wordHeads (Tier2.tapePrefix n z.2) = k ∧
        z.1 ∈ S (Tier2.tapePrefix n z.2)}) =
      (∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => wordHeads x = k),
        ν (stoppedSeedCell A x (S x))) * populationWordLikelihood μ p₀ p₁ q n k := by
  classical
  let words := Finset.univ.filter (fun x : Fin n → Bool => wordHeads x = k)
  let cells (x : Fin n → Bool) := populationInput p₀ p₁ q ⁻¹'
    {z : R × (ℕ → Bool) | z.1 ∈ S x ∧ A.stop z = n ∧ Tier2.tapePrefix n z.2 = x}
  have he : populationInput p₀ p₁ q ⁻¹'
      {z : R × (ℕ → Bool) | A.stop z = n ∧ wordHeads (Tier2.tapePrefix n z.2) = k ∧
        z.1 ∈ S (Tier2.tapePrefix n z.2)} = ⋃ x ∈ words, cells x := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hn,hk,hs⟩
      refine ⟨Tier2.tapePrefix n (populationInput p₀ p₁ q z).2, ?_, ?_⟩
      · simp [words,hk]
      · exact ⟨hs,hn,rfl⟩
    · rintro ⟨x,hx,hs,hn,hpx⟩
      have hk := (Finset.mem_filter.mp hx).2
      exact ⟨hn,by rwa [hpx],by rwa [hpx]⟩
  have hd : PairwiseDisjoint (↑words) cells := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    rintro z ⟨_,_,hpx⟩ ⟨_,_,hpy⟩
    exact hxy (hpx.symm.trans hpy)
  have hm : ∀ x ∈ words, MeasurableSet (cells x) := by
    intro x hx
    exact (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
      ((measurable_fst (hS x)).inter
        ((A.measurable_stop (measurableSet_singleton (n : ℕ∞))).inter
          (((Tier2.measurable_prefix n).comp measurable_snd) (measurableSet_singleton x))))
  rw [he, measure_biUnion_finset hd hm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [population_stopped_word_probability μ ν p₀ p₁ q h₀ h₁ hq A x (S x) (hS x)]
  rw [(Finset.mem_filter.mp hx).2]


end ThresholdHC.CriticalEntropy
