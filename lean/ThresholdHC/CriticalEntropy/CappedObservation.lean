import ThresholdHC.CriticalEntropy.FiniteObservation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem measurable_cappedTranscript {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) : Measurable (cappedTranscript A m) := by
  let f : ℕ × (Fin m → Bool) → CappedWord m := fun z =>
    ⟨⟨min z.1 m, Nat.lt_succ_of_le (min_le_right _ _)⟩,
      fun i => z.2 ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩⟩
  have hm : Measurable (fun z : R × (ℕ → Bool) =>
      f ((A.stop z).toNat,Tier2.tapePrefix m z.2)) :=
    (measurable_of_countable f).comp
      (((measurable_of_countable ENat.toNat).comp A.measurable_stop).prodMk
        ((Tier2.measurable_prefix m).comp measurable_snd))
  exact measurable_fst.prodMk hm

theorem cappedTranscript_of_stop {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m n : ℕ) (hnm : n ≤ m)
    (z : R × (ℕ → Bool)) (hn : A.stop z = n) :
    cappedTranscript A m z =
      (z.1,⟨⟨n,Nat.lt_succ_of_le hnm⟩,Tier2.tapePrefix n z.2⟩) := by
  have he : min (A.stop z).toNat m = n := by
    rw [hn, ENat.toNat_natCast, Nat.min_eq_left hnm]
  subst n
  rfl

theorem cappedTranscript_mem_cell {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) (z : R × (ℕ → Bool))
    (hcap : A.stop z ≤ m) (w : CappedWord m) (S : Set R) :
    cappedTranscript A m z ∈ S ×ˢ {w} ↔
      z.1 ∈ S ∧ A.stop z = w.1.val ∧ Tier2.tapePrefix w.1.val z.2 = w.2 := by
  rcases w with ⟨n,x⟩
  have hfin : A.stop z ≠ ⊤ := ne_top_of_le_ne_top (by simp) hcap
  have hlen : (A.stop z).toNat ≤ m := by
    simpa using ENat.toNat_le_toNat hcap (by simp)
  change z.1 ∈ S ∧ (cappedTranscript A m z).2 = ⟨n,x⟩ ↔ _
  constructor
  · rintro ⟨hs,hw⟩
    have hn := congrArg (fun v : CappedWord m => v.1.val) hw
    change min (A.stop z).toNat m = n.val at hn
    rw [Nat.min_eq_left hlen] at hn
    have hstop : A.stop z = n.val := by rw [← ENat.natCast_toNat hfin,hn]
    rw [cappedTranscript_of_stop A m n.val (Nat.le_of_lt_succ n.isLt) z hstop] at hw
    have hx : Tier2.tapePrefix n.val z.2 = x :=
      eq_of_heq (Sigma.mk.inj hw).2
    exact ⟨hs,hstop,hx⟩
  · rintro ⟨hs,hn,hx⟩
    refine ⟨hs,?_⟩
    rw [cappedTranscript_of_stop A m n.val (Nat.le_of_lt_succ n.isLt) z hn]
    simp only [hx]

theorem cappedTranscriptLaw_cell {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) (w : CappedWord m) (S : Set R) (hS : MeasurableSet S) :
    cappedTranscriptLaw μ ν p₀ p₁ q A m (S ×ˢ {w}) =
      ν (stoppedSeedCell A w.2 S) * populationWordLikelihood μ p₀ p₁ q w.1.val (wordHeads w.2) := by
  unfold cappedTranscriptLaw
  rw [Measure.map_apply ((measurable_cappedTranscript A m).comp
    (measurable_populationInput p₀ p₁ q h₀ h₁ hq)) (hS.prod (measurableSet_singleton w))]
  have he : (cappedTranscript A m ∘ populationInput p₀ p₁ q) ⁻¹' (S ×ˢ {w}) =
      populationInput p₀ p₁ q ⁻¹' {z : R × (ℕ → Bool) |
        z.1 ∈ S ∧ A.stop z = w.1.val ∧ Tier2.tapePrefix w.1.val z.2 = w.2} := by
    ext z
    exact cappedTranscript_mem_cell A m _ (hcap _) w S
  rw [he,population_stopped_word_probability μ ν p₀ p₁ q h₀ h₁ hq A w.2 S hS]

theorem stoppedReference_cell {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (m : ℕ)
    (w : CappedWord m) (S : Set R) (hS : MeasurableSet S) :
    stoppedReference ν A m (S ×ˢ {w}) = ν (stoppedSeedCell A w.2 S) := by
  unfold stoppedReference
  rw [Measure.restrict_apply (hS.prod (measurableSet_singleton w))]
  have he : (S ×ˢ {w}) ∩ {z : R × CappedWord m | (z.1,z.2.2) ∈ A.stopPrefix z.2.1.val} =
      stoppedSeedCell A w.2 S ×ˢ {w} := by
    ext z
    rcases z with ⟨r,v⟩
    constructor
    · rintro ⟨⟨hs,hv⟩,ha⟩
      have hv' : v = w := hv
      subst v
      exact ⟨⟨hs,ha⟩,rfl⟩
    · rintro ⟨⟨hs,ha⟩,hv⟩
      have hv' : v = w := hv
      subst v
      exact ⟨⟨hs,rfl⟩,ha⟩
  rw [he,Measure.prod_prod]
  simp

theorem measure_ext_prod_finite {R W : Type} [MeasurableSpace R] [MeasurableSpace W]
    [Fintype W] [MeasurableSingletonClass W] (P Q : Measure (R × W))
    (h : ∀ (w : W) (S : Set R), MeasurableSet S → P (S ×ˢ {w}) = Q (S ×ˢ {w})) : P = Q := by
  classical
  apply Measure.ext
  intro S hS
  let cells (w : W) := {r : R | (r,w) ∈ S} ×ˢ {w}
  have hm (w : W) : MeasurableSet {r : R | (r,w) ∈ S} :=
    (measurable_id.prodMk measurable_const) hS
  have he : S = ⋃ w : W, cells w := by ext z; simp [cells]
  have hd : Pairwise (fun i j => Disjoint (cells i) (cells j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨_,hi⟩ ⟨_,hj⟩
    exact hij (hi.symm.trans hj)
  rw [he,measure_iUnion hd (fun w => (hm w).prod (measurableSet_singleton w)),
    measure_iUnion hd (fun w => (hm w).prod (measurableSet_singleton w))]
  congr 1
  funext w
  exact h w _ (hm w)

instance stoppedReference_finite {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (m : ℕ) :
    IsFiniteMeasure (stoppedReference ν A m) := by
  unfold stoppedReference
  infer_instance

theorem cappedTranscriptLaw_density {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) :
    cappedTranscriptLaw μ ν p₀ p₁ q A m =
      (stoppedReference ν A m).withDensity (fun z =>
        populationWordLikelihood μ p₀ p₁ q z.2.1.val (wordHeads z.2.2)) := by
  apply measure_ext_prod_finite
  intro w S hS
  rw [cappedTranscriptLaw_cell μ ν p₀ p₁ q h₀ h₁ hq A m hcap w S hS,
    withDensity_apply _ (hS.prod (measurableSet_singleton w))]
  have he : (∫⁻ z in S ×ˢ {w}, populationWordLikelihood μ p₀ p₁ q z.2.1.val
      (wordHeads z.2.2) ∂stoppedReference ν A m) =
      ∫⁻ _z in S ×ˢ {w}, populationWordLikelihood μ p₀ p₁ q w.1.val
        (wordHeads w.2) ∂stoppedReference ν A m := by
    apply setLIntegral_congr_fun (hS.prod (measurableSet_singleton w))
    intro z hz
    dsimp only
    rw [show z.2 = w from hz.2]
  rw [he,setLIntegral_const,stoppedReference_cell ν A m w S hS,mul_comm]

theorem cappedTranscriptLaw_probability {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ) :
    IsProbabilityMeasure (cappedTranscriptLaw μ ν p₀ p₁ q A m) := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by unfold populationMeasure; infer_instance
  constructor
  rw [cappedTranscriptLaw, Measure.map_apply ((measurable_cappedTranscript A m).comp
    (measurable_populationInput p₀ p₁ q h₀ h₁ hq)) MeasurableSet.univ]
  simp

end ThresholdHC.CriticalEntropy
