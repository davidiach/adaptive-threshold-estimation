import ThresholdHC.ArbitraryLawAdaptation.TailPilotLaw

/-! The paid pilot uses labels `Nat.pair 0 i`; production uses
`Nat.pair 1 i`. The entire production stream and private seed retain their
joint law after any positive-probability finite pilot history. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.BlindUpper

theorem infinitePi_two_blocks {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] :
    (Measure.infinitePi (fun _ : ℕ => ν)).map
      (fun ω => ((fun i => ω (Nat.pair 0 i)), (fun i => ω (Nat.pair 1 i)))) =
      (Measure.infinitePi (fun _ : ℕ => ν)).prod (Measure.infinitePi (fun _ : ℕ => ν)) := by
  have hm : Measurable (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) := by fun_prop
  have he : (fun (ω : ℕ → X) => ((fun i => ω (Nat.pair 0 i)), (fun i => ω (Nat.pair 1 i)))) =
      (fun (z : ℕ → ℕ → X) => (z 0, z 1)) ∘ (fun ω j i => ω (Nat.pair j i)) := rfl
  rw [he, ← Measure.map_map (by fun_prop) hm, infinitePi_map_blocks ν]
  exact Measure.infinitePi_map_eval_prod (by decide : (0:ℕ) ≠ 1)

theorem seed_two_blocks {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (P : Measure R) (ν : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure ν] :
    (P.prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun z => ((fun i => z.2 (Nat.pair 0 i)), (z.1, fun i => z.2 (Nat.pair 1 i)))) =
      (Measure.infinitePi (fun _ : ℕ => ν)).prod (P.prod (Measure.infinitePi (fun _ : ℕ => ν))) := by
  let Q := Measure.infinitePi (fun _ : ℕ => ν)
  have hs : MeasurePreserving
      (fun ω : ℕ → X => ((fun i => ω (Nat.pair 0 i)), (fun i => ω (Nat.pair 1 i))))
      Q (Q.prod Q) := ⟨by fun_prop, infinitePi_two_blocks ν⟩
  have ha := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc P Q Q)
  have hb := (Measure.measurePreserving_swap (μ := P) (ν := Q)).prod (MeasurePreserving.id Q)
  have hc := measurePreserving_prodAssoc Q P Q
  exact (hc.comp (hb.comp (ha.comp ((MeasurePreserving.id P).prod hs)))).map_eq

theorem measurable_pilot_word (n : ℕ) (p : Reader) :
    Measurable (fun s : Table => (readBlock n p s).1) := by
  have he : (fun s : Table => (readBlock n p s).1) =
      (fun s => processHistory (populationPath (stopAt n p) s) n) :=
    funext fun s => (wordEstimator_history n p s).symm
  rw [he]
  exact (measurable_processHistory_fixed n).comp (measurable_populationPath _)

theorem measurable_seeded_word {R : Type} [MeasurableSpace R] (n : ℕ) (p : R → Reader)
    (hp : ∀ xs, Measurable (fun r => p r xs)) :
    Measurable (fun z : R × Table => (readBlock n (p z.1) z.2).1) := by
  have hpol : ∀ xs, Measurable (fun r => stopAt n (p r) xs) := by
    intro xs
    by_cases h : xs.length < n
    · simpa only [stopAt, ite_eq_left h, Function.comp_def] using
        (measurable_of_countable some).comp (hp xs)
    · simp only [stopAt, ite_eq_right h]
      exact measurable_const
  have he : (fun z : R × Table => (readBlock n (p z.1) z.2).1) =
      (fun z => processHistory (populationPath (stopAt n (p z.1)) z.2) n) :=
    funext fun z => (wordEstimator_history n (p z.1) z.2).symm
  rw [he]
  exact (measurable_processHistory_fixed n).comp (measurable_seeded_populationPath _ hpol)

theorem pilot_production_joint_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (n : ℕ) (p : Reader) :
    (originalSimulationLaw μ A q).map
      (fun z => ((readBlock n p (z.2 ∘ Nat.pair 0)).1, (z.1, z.2 ∘ Nat.pair 1))) =
      ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
        (fun s => (readBlock n p s).1)).prod (originalSimulationLaw μ A q) := by
  have h := seed_two_blocks A.randomLaw (originalPopulationTapeLaw μ q)
  have hmap := congrArg (fun Q => Q.map
    (Prod.map (fun s : Table => (readBlock n p s).1) id)) h
  rw [Measure.map_map ((measurable_pilot_word n p).prodMap measurable_id) (by fun_prop),
    ← Measure.map_prod_map _ _ (measurable_pilot_word n p) measurable_id,
    Measure.map_id] at hmap
  exact hmap

/-- A history restriction leaves the production input law multiplied only
by that history's probability. This also covers null histories. -/
theorem pilot_restrict_production_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (n : ℕ) (p : Reader) (xs : List Bool) :
    ((originalSimulationLaw μ A q).restrict
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => (z.1, z.2 ∘ Nat.pair 1)) =
      ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))
        {s | (readBlock n p s).1 = xs}) • originalSimulationLaw μ A q := by
  have : IsProbabilityMeasure (originalSimulationLaw μ A q) := by
    unfold originalSimulationLaw
    infer_instance
  have hm : Measurable (fun z : R × Table =>
      ((readBlock n p (z.2 ∘ Nat.pair 0)).1, (z.1, z.2 ∘ Nat.pair 1))) :=
    ((measurable_pilot_word n p).comp (by fun_prop)).prodMk (by fun_prop)
  have h := congrArg (fun Q => (Q.restrict ({xs} ×ˢ univ)).map Prod.snd)
    (pilot_production_joint_law μ A q n p)
  rw [Measure.restrict_map hm ((measurableSet_singleton xs).prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ, Measure.map_snd_prod,
    Measure.restrict_apply_univ, Measure.map_apply (measurable_pilot_word n p)
      (measurableSet_singleton xs), Measure.map_map measurable_snd hm] at h
  simpa only [Function.comp_def, Set.preimage, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_univ, and_true] using h

theorem pilot_history_probability {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (n : ℕ) (p : Reader) (xs : List Bool) :
    (originalSimulationLaw μ A q) {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs} =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))
        {s | (readBlock n p s).1 = xs} := by
  have : IsProbabilityMeasure (originalSimulationLaw μ A q) := by
    unfold originalSimulationLaw
    infer_instance
  have h := congrArg (fun Q : Measure (R × Table) => Q univ)
    (pilot_restrict_production_law μ A q n p xs)
  simpa only [Measure.map_apply (by fun_prop : Measurable
      (fun z : R × Table => (z.1, z.2 ∘ Nat.pair 1))) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one] using h

/-- Conditioning is normalization of the restriction. Every finite history
with nonzero probability leaves the complete production input law unchanged. -/
theorem pilot_conditional_production_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (n : ℕ) (p : Reader) (xs : List Bool)
    (hxs : (originalSimulationLaw μ A q)
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs} ≠ 0) :
    (((originalSimulationLaw μ A q)
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs})⁻¹ •
      (originalSimulationLaw μ A q).restrict
        {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => (z.1, z.2 ∘ Nat.pair 1)) = originalSimulationLaw μ A q := by
  have : IsProbabilityMeasure (originalSimulationLaw μ A q) := by
    unfold originalSimulationLaw
    infer_instance
  rw [Measure.map_smul _ (by fun_prop), pilot_restrict_production_law,
    ← pilot_history_probability μ A q n p xs, smul_smul,
    ENNReal.inv_mul_cancel hxs (measure_ne_top _ _), one_smul]

/-- A family of private seeds, one for each possible pilot word, permits
history-dependent seed spaces and distributions. After conditioning, the
selected seed and production stream have exactly the selected product law. -/
theorem pilot_selected_seed_law {R : List Bool → Type} [∀ xs, MeasurableSpace (R xs)]
    (P : ∀ xs, Measure (R xs)) [∀ xs, IsProbabilityMeasure (P xs)]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (n : ℕ) (p : Reader) (xs : List Bool)
    (hxs : ((Measure.infinitePi P).prod
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs} ≠ 0) :
    ((((Measure.infinitePi P).prod
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs})⁻¹ •
      ((Measure.infinitePi P).prod
        (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).restrict
        {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => (z.1 xs, z.2 ∘ Nat.pair 1)) =
      (P xs).prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) := by
  let A : AdaptiveEstimator (∀ ys, R ys) :=
    { randomLaw := Measure.infinitePi P
      probability := inferInstance
      policy := fun _ _ => none
      policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
      output := fun _ => 0
      output_measurable := measurable_const }
  have h := congrArg (fun Q => Q.map (Prod.map (fun r : ∀ ys, R ys => r xs) id))
    (pilot_conditional_production_law μ A q n p xs hxs)
  rw [Measure.map_map ((measurable_pi_apply xs).prodMap measurable_id) (by fun_prop)] at h
  change _ = ((Measure.infinitePi P).prod
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).map _ at h
  rw [← Measure.map_prod_map _ _ (measurable_pi_apply xs) measurable_id,
    Measure.infinitePi_map_eval, Measure.map_id] at h
  exact h

/-- The installed multi-depth pilot is an instance of the same joint law,
including its adaptively chosen coin labels and the entire private seed. -/
theorem pilotStage_production_joint_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (J m : ℕ) (ρ : ℝ) :
    (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q).map
      (fun z => (pilotStageWord J m ρ z.2, (z.1, z.2 ∘ Nat.pair 1))) =
      ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
        (fun s => (readBlock (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ)) s).1)).prod
      (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q) :=
  pilot_production_joint_law μ ((pilotStage S J m ρ).endpoint false) q
    (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ))

theorem pilotStage_conditional_production_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (J m : ℕ) (ρ : ℝ) (xs : List Bool)
    (hxs : (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q)
      {z | pilotStageWord J m ρ z.2 = xs} ≠ 0) :
    (((originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q)
      {z | pilotStageWord J m ρ z.2 = xs})⁻¹ •
      (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q).restrict
        {z | pilotStageWord J m ρ z.2 = xs}).map
      (fun z => (z.1, z.2 ∘ Nat.pair 1)) =
      originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q :=
  pilot_conditional_production_law μ ((pilotStage S J m ρ).endpoint false) q
    (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ)) xs hxs

theorem learnedStage_pilot_history {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (r : R) (s : Table) :
    (processHistory (populationPath ((S.endpoint false).policy r) s) S.cap).take S.pilotCost =
      (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1 := by
  change (processHistory (populationPath (stopAt S.cap (S.reader r)) s) S.cap).take _ = _
  rw [wordEstimator_history]
  let v := readBlock S.pilotCost (Nat.pair 0 ∘ S.pilot) s
  let u := readBlock S.continuationCost
    (Nat.pair 1 ∘ S.continuation (S.learnedLaw v.1) r) v.2
  have h : (readBlock S.cap (S.reader r) s).1 = v.1 ++ u.1 :=
    congrArg Prod.fst (ThresholdHC.LawAdaptation.readBlock_thenChoose
      S.pilotCost S.continuationCost (Nat.pair 0 ∘ S.pilot)
      (fun xs => Nat.pair 1 ∘ S.continuation (S.learnedLaw xs) r) s)
  rw [h]
  calc
    (v.1 ++ u.1).take S.pilotCost = v.1 := by
      rw [← show v.1.length = S.pilotCost from readBlock_length _ _ _, List.take_left]
    _ = _ := readBlock_relabel _ _ (fun _ _ h => (Nat.pair_eq_pair.mp h).2) _ _

/-- Joint observed pilot word and reported interval in the actual hidden-gap
experiment. The conditioning history is the paid chronological prefix. -/
theorem original_pilot_interval_law {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((processHistory z.2 S.cap).take S.pilotCost,
        ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2)))) =
      (originalSimulationLaw μ (S.endpoint false) q).map (fun z =>
        ((readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1, S.tableInterval z.1 z.2)) := by
  let A := S.endpoint false
  let F (z : R × ProcessTape) := ((processHistory z.2 S.cap).take S.pilotCost,
    (A.output z, (S.endpoint true).output z))
  have hF : Measurable F :=
    ((measurable_of_countable (fun xs : List Bool => xs.take S.pilotCost)).comp
      ((measurable_processHistory_fixed S.cap).comp measurable_snd)).prodMk
      (A.output_measurable.prodMk (S.endpoint true).output_measurable)
  have hg : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,z.2)) := by fun_prop
  have hp : Measurable (fun z : R × Table => (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  change (experimentLaw μ A q).map (F ∘ fun z => (z.1.1,z.2)) = _
  rw [← Measure.map_map hF hg, original_observable_simulation_law, Measure.map_map hF hp]
  apply congrArg (fun f => (originalSimulationLaw μ A q).map f)
  funext z
  change ((processHistory (populationPath ((S.endpoint false).policy z.1) z.2) S.cap).take _,
    ((S.endpoint false).output (z.1,populationPath ((S.endpoint false).policy z.1) z.2),
      (S.endpoint true).output (z.1,populationPath ((S.endpoint true).policy z.1) z.2))) = _
  rw [learnedStage_pilot_history, S.endpoint_output, S.endpoint_output]
  rfl

theorem measurable_selected_interval {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (xs : List Bool) :
    Measurable (fun z : R × Table => S.interval (S.learnedLaw xs) z.1
      (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := by
  have hi : Measurable (fun z : R × List Bool => S.interval (S.learnedLaw xs) z.1 z.2) :=
    measurable_from_prod_countable_left (S.interval_measurable _)
  exact hi.comp (measurable_fst.prodMk
    (measurable_seeded_word _ _ (S.continuation_measurable _)))

/-- After conditioning on a pilot history, the selected continuation runs on
the original independent private seed and fresh production tapes. This is an
execution-law identity; no statistical coverage premise is supplied. -/
theorem learnedStage_conditional_interval_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (xs : List Bool)
    (hxs : (originalSimulationLaw μ (S.endpoint false) q)
      {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs} ≠ 0) :
    (((originalSimulationLaw μ (S.endpoint false) q)
      {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs})⁻¹ •
      (originalSimulationLaw μ (S.endpoint false) q).restrict
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => S.tableInterval z.1 z.2) =
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := by
  let P := originalSimulationLaw μ (S.endpoint false) q
  let E := {z : R × Table | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}
  let Q := (P E)⁻¹ • P.restrict E
  let G := fun z : R × Table => S.interval (S.learnedLaw xs) z.1
    (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1
  have hE : MeasurableSet E := measurableSet_eq_fun
    ((measurable_pilot_word _ _).comp (by fun_prop)) measurable_const
  have hmem : ∀ᵐ z ∂Q, z ∈ E := Measure.ae_smul_measure (ae_restrict_mem hE) _
  have he : Q.map (fun z => S.tableInterval z.1 z.2) =
      Q.map (G ∘ fun z => (z.1, z.2 ∘ Nat.pair 1)) := by
    apply Measure.map_congr
    filter_upwards [hmem] with z hz
    change (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs at hz
    simp only [LearnedStage.tableInterval, hz, Function.comp_apply, G]
  change Q.map _ = P.map G
  rw [he, ← Measure.map_map (measurable_selected_interval S xs) (by fun_prop)]
  rw [show Q.map (fun z => (z.1, z.2 ∘ Nat.pair 1)) = P from
    pilot_conditional_production_law μ (S.endpoint false) q S.pilotCost S.pilot xs hxs]

end ThresholdHC.RobustContinuation
