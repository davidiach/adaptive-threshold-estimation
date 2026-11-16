import ThresholdHC.ArbitraryLawController.LogSchedule
import ThresholdHC.ArbitraryLawController.JointFailure

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RobustContinuation
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper

abbrev StageSeed (ρ δ : ℝ) (s : ℕ) :=
  MedianSeed ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s))

def idleStage {R : Type} [MeasurableSpace R] (S : LearnedStage R) (ρ : ℝ) : LearnedStage R :=
  { S with
    pilotCost := 0
    continuationCost := 0
    interval := fun _ _ _ => (0, ρ)
    interval_measurable := fun _ _ => measurable_const }

def stage (ρ δ : ℝ) (s : ℕ) : LearnedStage (StageSeed ρ δ s) :=
  let S := paidMedianStage ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s))
    (depth δ s) (repetitions δ s (depth δ s))
  if depth δ s = 0 then idleStage S ρ else S

theorem stage_active {ρ δ : ℝ} {s : ℕ} (h : 1 ≤ depth δ s) :
    stage ρ δ s = paidMedianStage ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s))
      (depth δ s) (repetitions δ s (depth δ s)) := by
  simp only [stage, ite_eq_right (by omega : depth δ s ≠ 0)]

theorem stage_idle {ρ δ : ℝ} {s : ℕ} (h : depth δ s = 0) :
    (stage ρ δ s).cap = 0 ∧
      (∀ r xs, (stage ρ δ s).historyInterval r xs = (0, ρ)) ∧
      (∀ r t, (stage ρ δ s).tableInterval r t = (0, ρ)) := by
  simp [stage, h, idleStage, LearnedStage.cap, LearnedStage.historyInterval, LearnedStage.tableInterval]

theorem stage_cap (ρ δ : ℝ) (s : ℕ) : (stage ρ δ s).cap ≤ stageCap s := by
  by_cases hz : depth δ s = 0
  · rw [(stage_idle hz).1]; omega
  · rw [stage_active (by omega : 1 ≤ depth δ s)]
    have hr : (0 : ℝ) < remaining δ s := by exact_mod_cast (remaining_bounds δ s).1
    have hc := median_reservations_le hr (4 * pilotGroups δ s (depth δ s))
    rw [Nat.floor_natCast] at hc
    rw [paidMedianStage, pilotStage_cap]
    exact (Nat.add_le_add_left hc _).trans_eq (remaining_bounds δ s).2.2

def pilotGood (μ : Measure Gap) (ρ δ : ℝ) (s : ℕ) (xs : List Bool) : Prop :=
  (∀ x, (μ.map Subtype.val) (Iic x) ≤ (stage ρ δ s).learnedLaw xs (Iic x)) ∧
    ∀ i, i < depth δ s → (stage ρ δ s).upper xs i ≤ pilotBound μ (depth δ s) ρ (i + 1)

def stageBad (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (s : ℕ) :
    Set (StageSeed ρ δ s × Table) :=
  {z | (depth δ s ≠ 0 ∧ ¬pilotGood μ ρ δ s
      (readBlock (stage ρ δ s).pilotCost (stage ρ δ s).pilot (z.2 ∘ Nat.pair 0)).1) ∨
    (stage ρ δ s).tableInterval z.1 z.2 ∈ intervalFailure (signMean μ q.val)}

theorem measurableSet_stageBad (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (s : ℕ) :
    MeasurableSet (stageBad μ q ρ δ s) := by
  unfold stageBad
  simp only [Set.ofPred_or, Set.ofPred_and]
  apply MeasurableSet.union
  · exact (MeasurableSet.const _).inter
      ((Set.to_countable {xs | ¬pilotGood μ ρ δ s xs}).measurableSet.preimage
        ((measurable_pilot_word _ _).comp (by fun_prop)))
  · exact measurable_tableInterval _ (measurableSet_intervalFailure _)

theorem stage_pilot_failure {ρ δ : ℝ} (hρ : 0 < ρ) (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (originalSimulationLaw μ ((stage ρ δ s).endpoint false) q)
      {z | ¬pilotGood μ ρ δ s
        (readBlock (stage ρ δ s).pilotCost (stage ρ δ s).pilot (z.2 ∘ Nat.pair 0)).1} ≤
      ENNReal.ofReal (stageFailure δ s / 2) := by
  let S := stage ρ δ s
  let T := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)
  let E := {t : Table | pilotGood μ ρ δ s (pilotStageWord (depth δ s)
    (repetitions δ s (depth δ s)) ρ t)}
  have hE : MeasurableSet E :=
    (Set.to_countable {xs | pilotGood μ ρ δ s xs}).measurableSet.preimage
      ((measurable_pilot_word _ _).comp (by fun_prop))
  have hf := stageFailure_pos hd s
  have hp : 1 - stageFailure δ s / 2 ≤ T.real E := by
    apply (original_pilotStage_event μ q
      (medianStage ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s)))
      (depth δ s) (repetitions δ s (depth δ s)) hρ hJ (repetitions_pos δ s _)
      (by positivity) (repetitions_pilot_error hd hu s hJ)).trans
    refine measureReal_mono (fun t ht => ?_) (measure_ne_top _ _)
    change pilotGood μ ρ δ s _
    rw [pilotGood, stage_active hJ]
    exact ⟨ht.2, fun i hi => (ht.1 i hi).2⟩
  have he : T Eᶜ ≤ ENNReal.ofReal (stageFailure δ s / 2) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    change T.real Eᶜ ≤ stageFailure δ s / 2
    rw [measureReal_compl hE]
    simpa using (show 1 - T.real E ≤ stageFailure δ s / 2 by linarith)
  have hS := stage_active (ρ := ρ) hJ
  change (S.randomLaw.prod T) _ ≤ _
  have hset : {z : StageSeed ρ δ s × Table | ¬pilotGood μ ρ δ s
      (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1} = Prod.snd ⁻¹' Eᶜ := by
    dsimp [S]
    rw [hS]
    rfl
  rw [hset, ← Measure.map_apply measurable_snd hE.compl, Measure.map_snd_prod]
  simpa only [show S.randomLaw univ = 1 from S.probability.measure_univ, one_smul] using he

theorem stage_failure {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (s : ℕ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q) :
    (originalSimulationLaw μ ((stage ρ δ s).endpoint false) q) (stageBad μ q ρ δ s) ≤
      ENNReal.ofReal (stageFailure δ s) := by
  by_cases hz : depth δ s = 0
  · have he : stageBad μ q ρ δ s = ∅ := by
      ext z
      simp only [stageBad, Set.mem_ofPred_eq, hz, ne_eq, not_true_eq_false, false_and,
        false_or, (stage_idle hz).2.2, intervalFailure, Set.mem_empty_iff_false, iff_false, not_or]
      exact ⟨not_lt.mpr (signMean_bounds μ q).1, not_lt.mpr hq⟩
    rw [he, measure_empty]
    exact zero_le
  · have hJ : 1 ≤ depth δ s := by omega
    have hr : (0 : ℝ) < remaining δ s := by exact_mod_cast (remaining_bounds δ s).1
    have hf := stageFailure_pos hd s
    have hbound := learnedStage_joint_failure_le μ (stage ρ δ s) q (pilotGood μ ρ δ s)
      (signMean μ q.val) (ENNReal.ofReal ((3/4 : ℝ) ^ (4 * pilotGroups δ s (depth δ s)) / 2)) (by
        intro xs hg
        rw [stage_active hJ]
        apply paidMedianStage_fixed_failure hρ hρ4 hr _ _ _ μ q hq xs
        simpa only [stage_active hJ] using hg.1)
    have he : stageBad μ q ρ δ s = {z | ¬pilotGood μ ρ δ s
        (readBlock (stage ρ δ s).pilotCost (stage ρ δ s).pilot (z.2 ∘ Nat.pair 0)).1 ∨
        (stage ρ δ s).tableInterval z.1 z.2 ∈ intervalFailure (signMean μ q.val)} := by
      ext z
      simp only [stageBad, hz, ne_eq, not_false_eq_true, true_and]
    rw [he]
    apply hbound.trans
    calc _ ≤ ENNReal.ofReal (stageFailure δ s / 2) + ENNReal.ofReal (stageFailure δ s / 2) :=
        add_le_add (stage_pilot_failure hρ hd hu s hJ μ q)
          (ENNReal.ofReal_le_ofReal (median_schedule_failure hd hu s hJ))
      _ = ENNReal.ofReal (stageFailure δ s) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end ThresholdHC.ArbitraryLawController
