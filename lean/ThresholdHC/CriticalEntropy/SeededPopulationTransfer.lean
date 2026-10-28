import ThresholdHC.CriticalEntropy.ObservablePopulation

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC.Tier3 ThresholdHC.Tier4
open scoped ENNReal

/-- The actual observable finite-prefix bound for an arbitrary measurable
seed and unrestricted natural-number labels, derived from the conditional
population bound. No fixed coin cap across seeds is assumed. -/
theorem observable_population_hellinger_bound {R D Ω : Type}
    [MeasurableSpace R] [MeasurableSpace D] [MeasurableSpace Ω]
    (ν : Measure R) [IsProbabilityMeasure ν] (μ : Measure D) [IsProbabilityMeasure μ]
    (P Q M : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (seed : Ω → R × (ℕ → D)) (tape : Ω → ProcessTape)
    (pol : R → List Bool → Option ℕ) (d q r s : D → ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : Tier5.MeasurableCreationPolicy pol) (hdm : Measurable d)
    (hqm : Measurable q) (hrm : Measurable r) (hsm : Measurable s)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (hss : ∀ x, 0 ≤ s x ∧ s x ≤ 1)
    (hP : Tier5.RealizesCreationPrefixes (ν.prod (Measure.infinitePi (fun _ : ℕ => μ)))
      P seed tape (fun z => pol z.1) (fun z i => d (z.2 i)) (fun z i => q (z.2 i)))
    (hQ : Tier5.RealizesCreationPrefixes (ν.prod (Measure.infinitePi (fun _ : ℕ => μ)))
      Q seed tape (fun z => pol z.1) (fun z i => d (z.2 i)) (fun z i => r (z.2 i)))
    (hM : Tier5.RealizesCreationPrefixes (ν.prod (Measure.infinitePi (fun _ : ℕ => μ)))
      M seed tape (fun z => pol z.1) (fun z i => d (z.2 i)) (fun z i => s (z.2 i)))
    (n : ℕ) (K c : ℝ)
    (hpoint : ∀ u : R,
      (1-realFiniteAffinity (creationPopulationWeight (n := n) μ (pol u) d q)
        (creationPopulationWeight μ (pol u) d r))*K ≤
      c*∑ w : Prefix n, creationPopulationWeight μ (pol u) d s w*ThresholdHC.workOf w) :
    (1-(hellingerAffinity
      (P.map (fun ω => ((seed ω).1,processPrefix n (tape ω))))
      (Q.map (fun ω => ((seed ω).1,processPrefix n (tape ω))))).toReal)*K ≤
      c*∫ ω, ThresholdHC.workOf (processPrefix n (tape ω)) ∂M := by
  let obs (ω : Ω) := ((seed ω).1,processPrefix n (tape ω))
  have hobs : Measurable obs := hs.fst.prodMk (measurable_processPrefix tape ht n)
  let : IsProbabilityMeasure (P.map obs) :=
    (Measure.isProbabilityMeasure_map_iff hobs.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure (Q.map obs) :=
    (Measure.isProbabilityMeasure_map_iff hobs.aemeasurable).2 inferInstance
  let p (u : R) := creationPopulationWeight (n := n) μ (pol u) d q
  let t (u : R) := creationPopulationWeight (n := n) μ (pol u) d r
  let v (u : R) := creationPopulationWeight (n := n) μ (pol u) d s
  have hpm (w) : Measurable (fun u => p u w) :=
    measurable_creationPopulationWeight μ pol hp d q hdm hqm w
  have htm (w) : Measurable (fun u => t u w) :=
    measurable_creationPopulationWeight μ pol hp d r hdm hrm w
  have hvm (w) : Measurable (fun u => v u w) :=
    measurable_creationPopulationWeight μ pol hp d s hdm hsm w
  have hpn (u) := creationPopulationWeight_total μ (pol u) d q hdm hqm hd hq (n := n)
  have htn (u) := creationPopulationWeight_total μ (pol u) d r hdm hrm hd hr (n := n)
  have hvn (u) := creationPopulationWeight_total μ (pol u) d s hdm hsm hd hss (n := n)
  have hv1 (u w) : v u w ≤ 1 := by
    rw [← (hvn u).2]
    exact Finset.single_le_sum (fun z hz => (hvn u).1 z) (Finset.mem_univ w)
  have hPk := observable_population_prefix_kernel ν μ P seed tape pol d q
    hs ht hp hdm hqm hd hq hP n
  have hQk := observable_population_prefix_kernel ν μ Q seed tape pol d r
    hs ht hp hdm hrm hd hr hQ n
  have hMk := observable_population_prefix_kernel ν μ M seed tape pol d s
    hs ht hp hdm hsm hd hss hM n
  have hb := finite_kernel_hellinger_bound ν (P.map obs) (Q.map obs) p t hpm htm
    (fun u => (hpn u).1) (fun u => (htn u).1) (fun u => (hpn u).2) (fun u => (htn u).2)
    hPk hQk (fun u => ∑ w, v u w*ThresholdHC.workOf w)
    (Tier5.integrable_kernel_work ν v hvm (fun u => (hvn u).1) hv1 ThresholdHC.workOf) K c hpoint
  have hf : Measurable (fun z : R × Prefix n => ThresholdHC.workOf z.2) :=
    (measurable_of_countable ThresholdHC.workOf).comp measurable_snd
  have hw := hMk (fun z => ThresholdHC.workOf z.2) hf
    ⟨n,fun z => by rw [abs_of_nonneg (workOf_nonneg z.2)]; exact workOf_le_length z.2⟩
  rw [integral_map hobs.aemeasurable hf.aestronglyMeasurable] at hw
  rw [← hw] at hb
  exact hb

end ThresholdHC.CriticalEntropy
