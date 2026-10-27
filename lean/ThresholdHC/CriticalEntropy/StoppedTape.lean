import ThresholdHC.CriticalEntropy.StoppedModel
import ThresholdHC.CriticalEntropy.BernoulliPrefix

/-!
Unused iid suffixes at observable stopping times. The product law is proved
by splitting at each deterministic prefix and summing over exact stopping
levels. No strong-Markov property or independence of restarts is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

theorem tapeDrop_map (p : unitInterval) (n : ℕ) :
    (Tier2.tapeMeasure p).map (tapeDrop n) = Tier2.tapeMeasure p := by
  unfold Tier2.tapeMeasure tapeDrop
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Nat.add_left_cancel h)

theorem prefix_drop_independent (p : unitInterval) (n : ℕ) :
    IndepFun (Tier2.tapePrefix n) (tapeDrop n) (Tier2.tapeMeasure p) := by
  have hi : iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) => ω i) (Tier2.tapeMeasure p) :=
    iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)
  have hd : Disjoint (Set.Iio n) (Set.Ici n) := Set.disjoint_left.mpr (by
    intro k hk hkn
    exact (not_lt_of_ge (show n ≤ k from hkn)) (show k < n from hk))
  have hh := hi.indepFun_set (Set.Iio n) (Set.Ici n) hd
    (fun i => measurable_pi_apply i)
  let f : (Set.Iio n → Bool) → (Fin n → Bool) := fun ω i => ω ⟨i.val, i.isLt⟩
  let g : (Set.Ici n → Bool) → (ℕ → Bool) := fun ω k => ω ⟨n+k, Nat.le_add_right n k⟩
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  exact hh.comp hf hg

theorem tape_split_map (p : unitInterval) (n : ℕ) :
    (Tier2.tapeMeasure p).map (fun ω => (Tier2.tapePrefix n ω, tapeDrop n ω)) =
      (Tier2.finiteMeasure p n).prod (Tier2.tapeMeasure p) := by
  rw [(prefix_drop_independent p n).map_prod_eq_prod_map_map
    (Tier2.measurable_prefix n).aemeasurable (measurable_tapeDrop n).aemeasurable,
    Tier2.prefix_map, tapeDrop_map]

theorem seeded_tape_split_map {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (n : ℕ) :
    (ν.prod (Tier2.tapeMeasure p)).map
        (fun z => ((z.1, Tier2.tapePrefix n z.2), tapeDrop n z.2)) =
      (ν.prod (Tier2.finiteMeasure p n)).prod (Tier2.tapeMeasure p) := by
  have hs : Measurable (fun ω => (Tier2.tapePrefix n ω, tapeDrop n ω)) :=
    (Tier2.measurable_prefix n).prodMk (measurable_tapeDrop n)
  have hm : (ν.prod (Tier2.tapeMeasure p)).map
      (Prod.map id (fun ω => (Tier2.tapePrefix n ω, tapeDrop n ω))) =
        ν.prod ((Tier2.finiteMeasure p n).prod (Tier2.tapeMeasure p)) := by
    rw [← Measure.map_prod_map ν (Tier2.tapeMeasure p) measurable_id hs,
      Measure.map_id, tape_split_map]
  have ha := (measurePreserving_prodAssoc ν (Tier2.finiteMeasure p n)
    (Tier2.tapeMeasure p)).symm
  rw [← ha.map_eq, ← hm, Measure.map_map (by fun_prop) (measurable_id.prodMap hs)]
  rfl

theorem measure_eq_tsum_stopping {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℕ∞) (hm : Measurable τ)
    (hfinite : P {z | τ z = ⊤} = 0) (s : Set Ω) (hs : MeasurableSet s) :
    P s = ∑' n : ℕ, P (s ∩ {z | τ z = n}) := by
  have ha : ∀ᵐ z ∂P, τ z ≠ ⊤ := by simpa only [ae_iff, not_not] using hfinite
  have he : s =ᵐ[P] ⋃ n : ℕ, s ∩ {z | τ z = n} := by
    filter_upwards [ha] with z hz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hz
    apply propext
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨n, h, hn.symm⟩, fun ⟨n, h, _⟩ => h⟩
  rw [measure_congr he, measure_iUnion]
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (ENat.natCast_inj.mp (hi.symm.trans hj))
  · intro n
    exact hs.inter (hm (measurableSet_singleton (n : ℕ∞)))

theorem seeded_prefix_drop_probability {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (n : ℕ)
    (s : Set (R × (Fin n → Bool))) (t : Set (ℕ → Bool))
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (ν.prod (Tier2.tapeMeasure p))
        ((fun z => (z.1, Tier2.tapePrefix n z.2)) ⁻¹' s ∩
          (fun z => tapeDrop n z.2) ⁻¹' t) =
      (ν.prod (Tier2.finiteMeasure p n)) s * Tier2.tapeMeasure p t := by
  have h := congrArg (fun μ => μ (s ×ˢ t)) (seeded_tape_split_map ν p n)
  have hm : Measurable (fun z : R × (ℕ → Bool) =>
      ((z.1, Tier2.tapePrefix n z.2), tapeDrop n z.2)) :=
    (measurable_fst.prodMk ((Tier2.measurable_prefix n).comp measurable_snd)).prodMk
      ((measurable_tapeDrop n).comp measurable_snd)
  rw [Measure.map_apply hm (hs.prod ht), Measure.prod_prod] at h
  exact h

theorem stopped_event_tail_probability {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (n : ℕ) (s : Set E) (t : Set (ℕ → Bool))
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (ν.prod (Tier2.tapeMeasure p))
        ((A.output ⁻¹' s ∩ {z | A.stop z = n}) ∩
          (fun z => tapeDrop n z.2) ⁻¹' t) =
      (ν.prod (Tier2.tapeMeasure p)) (A.output ⁻¹' s ∩ {z | A.stop z = n}) *
        Tier2.tapeMeasure p t := by
  let e := A.stopPrefix n ∩ A.outputPrefix n ⁻¹' s
  have he : MeasurableSet e :=
    (A.measurable_stopPrefix n).inter (A.measurable_outputPrefix n hs)
  have heq : (A.output ⁻¹' s ∩ {z | A.stop z = n}) =
      (fun z => (z.1, Tier2.tapePrefix n z.2)) ⁻¹' e := by
    ext z
    change (A.output z ∈ s ∧ A.stop z = n) ↔
      ((z.1, Tier2.tapePrefix n z.2) ∈ A.stopPrefix n ∧
        A.outputPrefix n (z.1, Tier2.tapePrefix n z.2) ∈ s)
    rw [A.stop_observable]
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨hn, (A.output_observable n z hn) ▸ hz⟩
    · rintro ⟨hn, hz⟩
      exact ⟨(A.output_observable n z hn).symm ▸ hz, hn⟩
  rw [heq, seeded_prefix_drop_probability ν p n e t he ht]
  congr 1
  have hm := congrArg (fun μ => μ e) (seeded_tape_prefix_map ν p n)
  rw [Measure.map_apply
    (measurable_id.prodMap (Tier2.measurable_prefix n)) he] at hm
  exact hm.symm

theorem stopped_output_suffix_probability {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E)
    (hfinite : (ν.prod (Tier2.tapeMeasure p)) {z | A.stop z = ⊤} = 0)
    (s : Set E) (t : Set (ℕ → Bool)) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (ν.prod (Tier2.tapeMeasure p)) (A.output ⁻¹' s ∩ stoppedSuffix A ⁻¹' t) =
      (ν.prod (Tier2.tapeMeasure p)) (A.output ⁻¹' s) * Tier2.tapeMeasure p t := by
  let P := ν.prod (Tier2.tapeMeasure p)
  have hpart := measure_eq_tsum_stopping P A.stop A.measurable_stop hfinite
    (A.output ⁻¹' s ∩ stoppedSuffix A ⁻¹' t)
    ((A.measurable_output hs).inter (measurable_stoppedSuffix A ht))
  change P _ = P _ * _
  rw [hpart]
  have he (n : ℕ) :
      (A.output ⁻¹' s ∩ stoppedSuffix A ⁻¹' t) ∩ {z | A.stop z = n} =
        (A.output ⁻¹' s ∩ {z | A.stop z = n}) ∩
          (fun z => tapeDrop n z.2) ⁻¹' t := by
    ext z
    constructor
    · rintro ⟨⟨hz, ht'⟩, hn⟩
      refine ⟨⟨hz, hn⟩, ?_⟩
      change A.stop z = (n : ℕ∞) at hn
      change tapeDrop (A.stop z).toNat z.2 ∈ t at ht'
      change tapeDrop n z.2 ∈ t
      rw [hn, ENat.toNat_natCast] at ht'
      exact ht'
    · rintro ⟨⟨hz, hn⟩, ht'⟩
      refine ⟨⟨hz, ?_⟩, hn⟩
      change A.stop z = (n : ℕ∞) at hn
      change tapeDrop n z.2 ∈ t at ht'
      change tapeDrop (A.stop z).toNat z.2 ∈ t
      rw [hn, ENat.toNat_natCast]
      exact ht'
  have hh (n : ℕ) :
      P ((A.output ⁻¹' s ∩ stoppedSuffix A ⁻¹' t) ∩ {z | A.stop z = n}) =
        P (A.output ⁻¹' s ∩ {z | A.stop z = n}) * Tier2.tapeMeasure p t := by
    rw [he]
    exact stopped_event_tail_probability ν p A n s t hs ht
  simp_rw [hh]
  rw [ENNReal.tsum_mul_right,
    ← measure_eq_tsum_stopping P A.stop A.measurable_stop hfinite
      (A.output ⁻¹' s) (A.measurable_output hs)]

theorem stopped_output_suffix_map {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E)
    (hfinite : (ν.prod (Tier2.tapeMeasure p)) {z | A.stop z = ⊤} = 0) :
    (ν.prod (Tier2.tapeMeasure p)).map (fun z => (A.output z, stoppedSuffix A z)) =
      ((ν.prod (Tier2.tapeMeasure p)).map A.output).prod (Tier2.tapeMeasure p) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (A.measurable_output.prodMk (measurable_stoppedSuffix A)) (hs.prod ht),
    Measure.prod_prod, Measure.map_apply A.measurable_output hs]
  exact stopped_output_suffix_probability ν p A hfinite s t hs ht

/-- Finite expected work implies termination under this same coin law. -/
theorem stopped_procedure_terminates {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R E)
    (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞) :
    (ν.prod (Tier2.tapeMeasure p)) {z | A.stop z = ⊤} = 0 := by
  have h := measure_eq_top_of_lintegral_ne_top
    (measurable_stoppedProcedureWork A).aemeasurable hfinite
  simpa only [stoppedProcedureWork, ENat.toENNReal_eq_top] using h

/-- The unused suffix is independent of both the output and actual work.
The parameter is fixed throughout, and finite expected work is a hypothesis
only under that parameter's law. -/
theorem stopped_marked_suffix_map {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E)
    (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞) :
    (ν.prod (Tier2.tapeMeasure p)).map
        (fun z => ((A.stop z, A.output z), stoppedSuffix A z)) =
      ((ν.prod (Tier2.tapeMeasure p)).map (fun z => (A.stop z, A.output z))).prod
        (Tier2.tapeMeasure p) :=
  stopped_output_suffix_map ν p (stoppedWithWork A)
    (stopped_procedure_terminates ν p A hfinite)

end ThresholdHC.CriticalEntropy
