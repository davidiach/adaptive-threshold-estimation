import ThresholdHC.RobustContinuation.PilotIndependence

/-! Conditional and unconditional coverage transfer for the actual chronological
paid stage. These execution lemmas are instantiated by the concrete median. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.BlindUpper

def intervalFailure (θ : ℝ) : Set (ℝ × ℝ) := {I | θ < I.1 ∨ I.2 < θ}

theorem measurableSet_intervalFailure (θ : ℝ) : MeasurableSet (intervalFailure θ) :=
  (measurableSet_lt measurable_const measurable_fst).union
    (measurableSet_lt measurable_snd measurable_const)

theorem intervalFailure_center (v r θ : ℝ) :
    (v-r, v+r) ∈ intervalFailure θ ↔ r < |v-θ| := by
  simp only [intervalFailure, mem_setOf_eq, lt_abs]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

theorem measurable_tableInterval {R : Type} [MeasurableSpace R] (S : LearnedStage R) :
    Measurable (fun z : R × Table => S.tableInterval z.1 z.2) := by
  have hi : Measurable (fun z : R × List Bool => S.historyInterval z.1 z.2) :=
    measurable_from_prod_countable_left S.measurable_historyInterval
  have hw := measurable_seeded_word S.cap S.reader S.measurable_reader
  convert hi.comp (measurable_fst.prodMk hw) using 1
  funext z
  exact (S.interval_readBlock z.1 z.2).symm

theorem learnedStage_restrict_interval_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (xs : List Bool) :
    ((originalSimulationLaw μ (S.endpoint false) q).restrict
      {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => S.tableInterval z.1 z.2) =
      ((originalSimulationLaw μ (S.endpoint false) q)
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}) •
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := by
  let P := originalSimulationLaw μ (S.endpoint false) q
  let E := {z : R × Table | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}
  let G := fun z : R × Table => S.interval (S.learnedLaw xs) z.1
    (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1
  have hE : MeasurableSet E := measurableSet_eq_fun
    ((measurable_pilot_word _ _).comp (by fun_prop)) measurable_const
  have he : (P.restrict E).map (fun z => S.tableInterval z.1 z.2) =
      (P.restrict E).map (G ∘ fun z => (z.1, z.2 ∘ Nat.pair 1)) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hE] with z hz
    change (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs at hz
    simp only [LearnedStage.tableInterval, hz, Function.comp_apply, G]
  change (P.restrict E).map _ = (P E) • P.map G
  rw [he, ← Measure.map_map (measurable_selected_interval S xs) (by fun_prop)]
  rw [show (P.restrict E).map (fun z => (z.1, z.2 ∘ Nat.pair 1)) = (P E) • P from by
    have hp := pilot_restrict_production_law μ (S.endpoint false) q S.pilotCost S.pilot xs
    rw [← pilot_history_probability μ (S.endpoint false) q S.pilotCost S.pilot xs] at hp
    exact hp]
  exact Measure.map_smul _ (measurable_selected_interval S xs).aemeasurable

/-- Restriction to the paid pilot prefix commutes with the exact joint-law
bridge to the hidden-gap experiment, including zero-probability histories. -/
theorem original_restrict_interval_law {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (xs : List Bool) :
    ((experimentLaw μ (S.endpoint false) q).restrict
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs}).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2),
        (S.endpoint true).output (z.1.1,z.2))) =
      ((originalSimulationLaw μ (S.endpoint false) q).restrict
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}).map
        (fun z => S.tableInterval z.1 z.2) := by
  have h := congrArg (fun Q : Measure (List Bool × (ℝ × ℝ)) =>
    (Q.restrict ({xs} ×ˢ univ)).map Prod.snd) (original_pilot_interval_law S μ q)
  have ho : Measurable (fun z : PopulationSeed R × ProcessTape =>
      ((processHistory z.2 S.cap).take S.pilotCost,
        ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2)))) := by
    have hi : Measurable (fun z : PopulationSeed R × ProcessTape =>
        ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) :=
      ((S.endpoint false).output_measurable.prodMk
      (S.endpoint true).output_measurable).comp (measurable_fst.fst.prodMk measurable_snd)
    exact ((measurable_of_countable (fun w : List Bool => w.take S.pilotCost)).comp
      ((measurable_processHistory_fixed S.cap).comp measurable_snd)).prodMk hi
  have hs : Measurable (fun z : R × Table =>
      ((readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1, S.tableInterval z.1 z.2)) :=
    ((measurable_pilot_word _ _).comp (by fun_prop)).prodMk (measurable_tableInterval S)
  rw [Measure.restrict_map ho ((measurableSet_singleton xs).prod MeasurableSet.univ),
    Measure.restrict_map hs ((measurableSet_singleton xs).prod MeasurableSet.univ),
    Measure.map_map measurable_snd ho, Measure.map_map measurable_snd hs] at h
  simpa only [Function.comp_def, Set.preimage, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_univ, and_true] using h

theorem measurable_endpoints {R : Type} [MeasurableSpace R] (S : LearnedStage R) :
    Measurable (fun z : PopulationSeed R × ProcessTape =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) :=
  ((S.endpoint false).output_measurable.prodMk (S.endpoint true).output_measurable).comp
    (measurable_fst.fst.prodMk measurable_snd)

theorem original_pilot_probability {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (xs : List Bool) :
    (experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs} =
      (originalSimulationLaw μ (S.endpoint false) q)
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs} := by
  have h := congrArg (fun Q : Measure (ℝ × ℝ) => Q univ)
    (original_restrict_interval_law S μ q xs)
  simpa only [Measure.map_apply (measurable_endpoints S) MeasurableSet.univ,
    Measure.map_apply (measurable_tableInterval S) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ] using h

theorem original_conditional_interval_law {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (xs : List Bool)
    (hxs : (experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs} ≠ 0) :
    (((experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs})⁻¹ •
      (experimentLaw μ (S.endpoint false) q).restrict
        {z | (processHistory z.2 S.cap).take S.pilotCost = xs}).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) =
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := by
  rw [Measure.map_smul _ (measurable_endpoints S).aemeasurable,
    original_restrict_interval_law, learnedStage_restrict_interval_law,
    ← original_pilot_probability, smul_smul,
    ENNReal.inv_mul_cancel hxs (measure_ne_top _ _), one_smul]

/-- A bound for every valid history integrates to stage coverage. Invalid
histories are charged at their actual probability, without conditioning on a
null event or assuming independence of the learned law and the pilot. -/
theorem learnedStage_failure_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (good : List Bool → Prop) (θ : ℝ) (δ : ℝ≥0∞)
    (hf : ∀ xs, good xs →
      ((originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1))
        (intervalFailure θ) ≤ δ) :
    ((experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure θ) ≤
      (originalSimulationLaw μ (S.endpoint false) q)
        {z | ¬good (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1} + δ := by
  classical
  let P := originalSimulationLaw μ (S.endpoint false) q
  let ν := (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
    (fun s => (readBlock S.pilotCost S.pilot s).1)
  have : IsProbabilityMeasure P := by dsimp [P, originalSimulationLaw]; infer_instance
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let F := fun z : List Bool × (R × Table) => S.interval (S.learnedLaw z.1) z.2.1
    (readBlock S.continuationCost (S.continuation (S.learnedLaw z.1) z.2.1) z.2.2).1
  have hF : Measurable F := measurable_from_prod_countable_right (measurable_selected_interval S)
  let J := fun z : R × Table => ((readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1,
    (z.1, z.2 ∘ Nat.pair 1))
  have hJ : Measurable J := ((measurable_pilot_word _ _).comp (by fun_prop)).prodMk (by fun_prop)
  have hj : P.map J = ν.prod P := pilot_production_joint_law μ (S.endpoint false) q S.pilotCost S.pilot
  have hbad : P {z | ¬good (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1} =
      ν {xs | ¬good xs} := by
    have h := congrArg (fun Q => Q ({xs | ¬good xs} ×ˢ univ)) hj
    rw [Measure.map_apply hJ ((Set.to_countable _).measurableSet.prod MeasurableSet.univ),
      Measure.prod_prod, measure_univ, mul_one] at h
    simpa only [J, Set.preimage, Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true] using h
  rw [S.original_interval_law, hbad]
  change (P.map (F ∘ J)) (intervalFailure θ) ≤ _
  rw [← Measure.map_map hF hJ, hj,
    Measure.map_apply hF (measurableSet_intervalFailure θ),
    Measure.prod_apply (hF (measurableSet_intervalFailure θ))]
  calc
    _ ≤ ∫⁻ xs, ({xs | ¬good xs}.indicator (fun _ => (1 : ℝ≥0∞))) xs + δ ∂ν := by
      apply lintegral_mono
      intro xs
      by_cases hg : good xs
      · simp only [Set.indicator_of_notMem (show xs ∉ {xs | ¬good xs} by simpa), zero_add]
        simpa only [Measure.map_apply (measurable_selected_interval S xs)
          (measurableSet_intervalFailure θ), F, Set.preimage, Set.mem_setOf_eq] using hf xs hg
      · simpa only [Set.indicator_of_mem (show xs ∈ {xs | ¬good xs} from hg)] using
          (show P (Prod.mk xs ⁻¹' F ⁻¹' intervalFailure θ) ≤ 1 + δ from
            prob_le_one.trans le_self_add)
    _ = ν {xs | ¬good xs} + δ := by
      rw [lintegral_add_left (measurable_const.indicator (Set.to_countable _).measurableSet),
        lintegral_indicator (Set.to_countable _).measurableSet]
      simp

end ThresholdHC.RobustContinuation
