import ThresholdHC.RobustContinuation.PilotIndependence

/-! Transfer of pilot events from the coin array to the experiment of the
whole learning stage.

For every learning stage and every property of words, the probability under
the original hidden-gap experiment of the stage that the paid chronological
prefix of the observed history has the property equals the probability, on
the coin array of the original simulation law, that the pilot's word on the
coins `Nat.pair 0 i` has it. The pilot does not read the private seed, so the
seed integrates out. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StagePilotLaw
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.BlindUpper ThresholdHC.RobustContinuation

variable {R : Type} [MeasurableSpace R]

/-- The paid chronological prefix of the observed history, as a function of
the observed pair of private seed and process tape, is measurable. -/
theorem measurable_pilot_prefix (S : LearnedStage R) :
    Measurable (fun w : R × ProcessTape => (processHistory w.2 S.cap).take S.pilotCost) :=
  (measurable_of_countable (fun xs : List Bool => xs.take S.pilotCost)).comp
    ((measurable_processHistory_fixed S.cap).comp measurable_snd)

/-- Every property of the paid chronological prefix has the same probability
under the original hidden-gap experiment of the stage as the same property of
the pilot's word under the original simulation law. -/
theorem pilot_prefix_simulation (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (good : List Bool → Prop) :
    (experimentLaw μ (S.endpoint false) q)
        {z | good ((processHistory z.2 S.cap).take S.pilotCost)} =
      (originalSimulationLaw μ (S.endpoint false) q)
        {z | good (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1} := by
  let A := S.endpoint false
  let E : Set (R × ProcessTape) := {w | good ((processHistory w.2 S.cap).take S.pilotCost)}
  have hE : MeasurableSet E :=
    (Set.to_countable {xs : List Bool | good xs}).measurableSet.preimage
      (measurable_pilot_prefix S)
  have h := congrArg (fun P : Measure (R × ProcessTape) => P E)
    (original_observable_simulation_law μ A q)
  have hm : Measurable (fun z : R × Table => (z.1, populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun w => measurable_to_countable' (A.policy_measurable w)))
  simp only [Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) hE,
    Measure.map_apply hm hE] at h
  refine h.trans ?_
  congr 1
  ext z
  change good ((processHistory (populationPath ((S.endpoint false).policy z.1) z.2) S.cap).take
    S.pilotCost) ↔ _
  rw [learnedStage_pilot_history]
  exact Iff.rfl

/-- Every property of the paid chronological prefix has the same probability
under the original hidden-gap experiment of the stage as the same property of
the pilot's word on the coin array. -/
theorem pilot_prefix_tape (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (good : List Bool → Prop) :
    (experimentLaw μ (S.endpoint false) q)
        {z | good ((processHistory z.2 S.cap).take S.pilotCost)} =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))
        {s | good (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1} := by
  let T := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)
  let E := {s : Table | good (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1}
  have hE : MeasurableSet E :=
    (Set.to_countable {xs : List Bool | good xs}).measurableSet.preimage
      ((measurable_pilot_word _ _).comp (by fun_prop))
  rw [pilot_prefix_simulation S μ q good]
  change (S.randomLaw.prod T) (Prod.snd ⁻¹' E) = T E
  have : IsProbabilityMeasure S.randomLaw := S.probability
  rw [← Measure.map_apply measurable_snd hE, Measure.map_snd_prod, measure_univ, one_smul]

/-- The same transfer, for the real-valued probabilities. -/
theorem pilot_prefix_tape_real (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (good : List Bool → Prop) :
    (experimentLaw μ (S.endpoint false) q).real
        {z | good ((processHistory z.2 S.cap).take S.pilotCost)} =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {s | good (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1} :=
  congrArg ENNReal.toReal (pilot_prefix_tape S μ q good)

end ThresholdHC.StagePilotLaw
