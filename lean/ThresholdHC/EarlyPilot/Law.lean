import ThresholdHC.EarlyPilot.Estimator

/-! The early-stopping pilot under the law of the original experiment.

Everything here holds for every family of estimators that meets
`IsEarlyPilot`, through the pathwise identities of the predicate alone.

* The event (A8): the certificates on table paths are those of the full
  pilot, so the coin-array event of the full pilot transfers to the original
  hidden-gap experiment as for `observable_pilot_event`.
* Expected work: on a table the pilot buys `sum_j sum_k probeFlips`, and each
  probe's charge is at most `min(b, probeWork M)`, whose mean on a stream of
  fresh coins is at most `min(b, M W)`, with `W` the work envelope integral.
The easy-law bounds, for laws whose gaps are all at least `a`, are in
`Easy.lean`. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace ThresholdHC.EarlyPilot
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation ThresholdHC.CriticalEntropy

/-! ### The event (A8) -/

theorem early_pilot_event_holds : EarlyPilotEventStatement := by
  intro J m ρ A hA μ _ q i₀ ε hρ hJ hm hε hmε
  obtain ⟨hpol, -, -, hout⟩ := hA
  let S : Set (Unit × ProcessTape) := {y | ∀ i, i < J →
    μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ (A i).output y ∧
      (A i).output y ≤ pilotBound μ J ρ (i + 1)}
  have hSeq : S = ⋂ i ∈ Finset.range J,
      ({y | μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ (A i).output y} ∩
        {y | (A i).output y ≤ pilotBound μ J ρ (i + 1)}) := by
    ext y
    simp [S]
  have hS : MeasurableSet S := by
    rw [hSeq]
    exact Finset.measurableSet_biInter _ fun i _ =>
      (measurableSet_le measurable_const (A i).output_measurable).inter
        (measurableSet_le (A i).output_measurable measurable_const)
  have hg : Measurable (fun z : PopulationSeed Unit × ProcessTape => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hp : Measurable (fun z : Unit × Table => (z.1, populationPath ((A i₀).policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath (A i₀).policy
      (fun xs => measurable_to_countable' ((A i₀).policy_measurable xs)))
  have h1 : (experimentLaw μ (A i₀) q).real {z | ∀ i, i < J →
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ (A i).output (z.1.1, z.2) ∧
        (A i).output (z.1.1, z.2) ≤ pilotBound μ J ρ (i + 1)} =
      ((experimentLaw μ (A i₀) q).map (fun z => (z.1.1, z.2))).real S :=
    (map_measureReal_apply hg hS).symm
  have hpre : (fun z : Unit × Table => (z.1, populationPath ((A i₀).policy z.1) z.2)) ⁻¹' S =
      Set.univ ×ˢ {s : Table | ((), populationPath ((A i₀).policy ()) s) ∈ S} := by
    ext ⟨u, s⟩
    simp
  rw [h1, original_observable_simulation_law, map_measureReal_apply hp hS, hpre]
  unfold originalSimulationLaw
  rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul, ← measureReal_def]
  refine (original_pilot_event μ q J m hρ hJ hm hε hmε measurable_pilotStreams
    (pilotStreams_law μ q)).trans (measureReal_mono ?_)
  intro s hs i hi
  have hpi : (A i₀).policy = (A i).policy := (hpol i₀).trans (hpol i).symm
  obtain ⟨hs1, hs2⟩ := hs i hi
  change μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
      (A i).output ((), populationPath ((A i₀).policy ()) s) ∧
    (A i).output ((), populationPath ((A i₀).policy ()) s) ≤ pilotBound μ J ρ (i + 1)
  rw [hpi, hout s i hi]
  exact ⟨hs1 _ _, hs2⟩

/-! ### Expected work -/

/-- The stream of probe `k` of depth `j + 1` is a stream of fresh coins. -/
theorem pilotStream_law (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (j k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
        (fun s => pilotStreams s j k) =
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) := by
  have he : (fun s : ℕ → ℕ → Bool => pilotStreams s j k) =
      (fun z : ℕ → ℕ → ℕ → Bool => z k) ∘ (fun z : ℕ → ℕ → ℕ → ℕ → Bool => z j) ∘ pilotStreams :=
    rfl
  rw [he, ← Measure.map_map (measurable_pi_apply k)
      ((measurable_pi_apply j).comp measurable_pilotStreams),
    ← Measure.map_map (measurable_pi_apply j) measurable_pilotStreams, pilotStreams_law,
    Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]

theorem measurable_pilotStream (j k : ℕ) :
    Measurable (fun s : ℕ → ℕ → Bool => pilotStreams s j k) :=
  (measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_pilotStreams)

/-- The charge of a probe is at most its budget and the work of `M` coins. -/
theorem probeFlips_le_min (J b M : ℕ) (ω : ℕ → ℕ → Bool) :
    probeFlips J b M ω ≤ min b (probeWork J ω M) :=
  min_le_min_left b (probeWork_mono J ω (probeHorizon_le J M ω))

theorem measurable_probeCharge (J b M : ℕ) :
    Measurable (fun ω : ℕ → ℕ → Bool => ((min b (probeWork J ω M) : ℕ) : ℝ)) :=
  (measurable_of_countable (fun n : ℕ => ((min b n : ℕ) : ℝ))).comp (measurable_probeWork J M)

theorem integrable_probeCharge {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] (J b M : ℕ) {f : X → ℕ → ℕ → Bool} (hf : Measurable f) :
    Integrable (fun x => ((min b (probeWork J (f x) M) : ℕ) : ℝ)) P :=
  integrable_of_abs_bound P _ ((measurable_probeCharge J b M).comp hf) b fun x => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast min_le_left _ _

/-- On a stream of fresh coins of the original population, the mean of
`min(b, work of the first M coins)` is at most `min(b, M W)`; by
`probeFlips_le_min` this bounds the mean charge of a probe with budget `b` and
coin cap `M`. -/
theorem probe_expected_charge (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J b M : ℕ) :
    ∫ ω, ((min b (probeWork J ω M) : ℕ) : ℝ)
        ∂Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) ≤
      min (b : ℝ) ((M : ℝ) * ∫ d : Gap, tailWorkEnvelope J d ∂μ) := by
  set ν := originalPopulationTapeLaw μ q
  have hint := integrable_probeCharge (Measure.infinitePi (fun _ : ℕ => ν)) J b M measurable_id
  refine le_min ?_ ?_
  · have h := integral_mono hint (integrable_const (b : ℝ)) fun ω => by
      change ((min b (probeWork J ω M) : ℕ) : ℝ) ≤ (b : ℝ)
      exact_mod_cast min_le_left _ _
    simpa using h
  · have h := integral_mono hint (integrable_probeWork ν J M) fun ω => by
      change ((min b (probeWork J ω M) : ℕ) : ℝ) ≤ (probeWork J ω M : ℝ)
      exact_mod_cast min_le_right _ _
    rw [stream_expected_work ν J M] at h
    exact h.trans (mul_le_mul_of_nonneg_left (original_tail_expected_work μ q J)
      (Nat.cast_nonneg _))

/-- The bound of the charges of all probes on a table. -/
def chargeBound (J m M : ℕ) (s : Table) : ℝ :=
  ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range m,
    ((min (pilotBudget J (j + 1)) (probeWork (j + 1) (pilotStreams s j k) M) : ℕ) : ℝ)

theorem measurable_chargeBound (J m M : ℕ) : Measurable (chargeBound J m M) :=
  Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
    (measurable_probeCharge _ _ _).comp (measurable_pilotStream j k)

theorem chargeBound_nonneg (J m M : ℕ) (s : Table) : 0 ≤ chargeBound J m M s :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem work_le_chargeBound (J m M : ℕ) (s : Table) :
    ((∑ j ∈ Finset.range J, ∑ k ∈ Finset.range m,
        probeFlips (j + 1) (pilotBudget J (j + 1)) M (pilotStreams s j k) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (chargeBound J m M s) := by
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold chargeBound
  push_cast
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => by
    exact_mod_cast probeFlips_le_min _ _ _ _

theorem integral_chargeBound_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J m M : ℕ) :
    ∫ s, chargeBound J m M s ∂Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) ≤
      (m : ℝ) * ∑ j ∈ Finset.range J,
        min (pilotBudget J (j + 1) : ℝ) ((M : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ) := by
  set P := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)
  have hint : ∀ j k, Integrable (fun s : Table =>
      ((min (pilotBudget J (j + 1)) (probeWork (j + 1) (pilotStreams s j k) M) : ℕ) : ℝ)) P :=
    fun j k => integrable_probeCharge P _ _ _ (measurable_pilotStream j k)
  have hterm : ∀ j k, ∫ s, ((min (pilotBudget J (j + 1))
      (probeWork (j + 1) (pilotStreams s j k) M) : ℕ) : ℝ) ∂P ≤
        min (pilotBudget J (j + 1) : ℝ) ((M : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ) := by
    intro j k
    have hmap := integral_map (μ := P) (measurable_pilotStream j k).aemeasurable
      (measurable_probeCharge (j + 1) (pilotBudget J (j + 1)) M).aestronglyMeasurable
    rw [pilotStream_law] at hmap
    rw [← hmap]
    exact probe_expected_charge μ q (j + 1) (pilotBudget J (j + 1)) M
  unfold chargeBound
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  calc ∑ j ∈ Finset.range J, ∫ s, ∑ k ∈ Finset.range m,
        ((min (pilotBudget J (j + 1)) (probeWork (j + 1) (pilotStreams s j k) M) : ℕ) : ℝ) ∂P
      = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range m, ∫ s,
        ((min (pilotBudget J (j + 1)) (probeWork (j + 1) (pilotStreams s j k) M) : ℕ) : ℝ) ∂P :=
        Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hint j k
    _ ≤ ∑ j ∈ Finset.range J, ∑ _k ∈ Finset.range m,
        min (pilotBudget J (j + 1) : ℝ) ((M : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
    _ = (m : ℝ) * ∑ j ∈ Finset.range J,
        min (pilotBudget J (j + 1) : ℝ) ((M : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem early_pilot_work_holds : EarlyPilotWorkStatement := by
  intro J m ρ A hA μ _ q i
  obtain ⟨-, -, hwork, -⟩ := hA
  set M := pilotCoinCap J ρ
  set P := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) with hP
  rw [original_expectedWork_simulation]
  calc ∫⁻ z, totalProcessWork (populationPath ((A i).policy z.1) z.2) ∂originalSimulationLaw μ (A i) q
      ≤ ∫⁻ z, ENNReal.ofReal (chargeBound J m M z.2) ∂originalSimulationLaw μ (A i) q := by
        refine lintegral_mono fun z => ?_
        change totalProcessWork (populationPath ((A i).policy ()) z.2) ≤ _
        rw [hwork z.2 i]
        exact work_le_chargeBound J m M z.2
    _ = ∫⁻ s, ENNReal.ofReal (chargeBound J m M s) ∂P := by
        rw [hP, ← originalSimulationLaw_coins μ (A i) q,
          lintegral_map (measurable_chargeBound J m M).ennreal_ofReal measurable_snd]
    _ = ENNReal.ofReal (∫ s, chargeBound J m M s ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_of_abs_bound P _ (measurable_chargeBound J m M)
            (∑ j ∈ Finset.range J, ∑ _k ∈ Finset.range m, (pilotBudget J (j + 1) : ℝ)) fun s => by
              rw [abs_of_nonneg (chargeBound_nonneg J m M s)]
              exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => by
                exact_mod_cast min_le_left _ _)
          (ae_of_all _ (chargeBound_nonneg J m M))).symm
    _ ≤ ENNReal.ofReal ((m : ℝ) * ∑ j ∈ Finset.range J,
        min (pilotBudget J (j + 1) : ℝ) ((M : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ)) :=
        ENNReal.ofReal_le_ofReal (integral_chargeBound_le μ q J m M)

end ThresholdHC.EarlyPilot
