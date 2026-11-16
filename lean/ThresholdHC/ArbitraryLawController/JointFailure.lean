import ThresholdHC.RobustContinuation.PaidMedian

/-! Charge a bad pilot only once, while retaining both coverage and the
pilot certificate on the same event. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.RobustContinuation ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open ThresholdHC.HardBudget

theorem learnedStage_joint_failure_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (good : List Bool → Prop) (θ : ℝ) (δ : ℝ≥0∞)
    (hf : ∀ xs, good xs →
      ((originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1))
        (intervalFailure θ) ≤ δ) :
    (originalSimulationLaw μ (S.endpoint false) q)
      {z | ¬good (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 ∨
        S.tableInterval z.1 z.2 ∈ intervalFailure θ} ≤
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
    simpa only [J, Set.preimage, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true] using h
  let E : Set (List Bool × (R × Table)) := {z | ¬good z.1 ∨ F z ∈ intervalFailure θ}
  have hE : MeasurableSet E :=
    (((Set.to_countable {xs | ¬good xs}).measurableSet).preimage measurable_fst).union
      (hF (measurableSet_intervalFailure θ))
  change P (J ⁻¹' E) ≤ _
  rw [hbad, ← Measure.map_apply hJ hE, hj, Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ xs, ({xs | ¬good xs}.indicator (fun _ => (1 : ℝ≥0∞))) xs + δ ∂ν := by
      apply lintegral_mono
      intro xs
      by_cases hg : good xs
      · simp only [Set.indicator_of_notMem (show xs ∉ {xs | ¬good xs} by simpa), zero_add]
        simpa only [Measure.map_apply (measurable_selected_interval S xs)
          (measurableSet_intervalFailure θ), E, F, Set.preimage, Set.mem_ofPred_eq,
          hg, not_true_eq_false, false_or] using hf xs hg
      · simpa only [Set.indicator_of_mem (show xs ∈ {xs | ¬good xs} from hg)] using
          (show P (Prod.mk xs ⁻¹' E) ≤ 1 + δ from prob_le_one.trans le_self_add)
    _ = ν {xs | ¬good xs} + δ := by
      rw [lintegral_add_left (measurable_const.indicator (Set.to_countable _).measurableSet),
        lintegral_indicator (Set.to_countable _).measurableSet]
      simp

end ThresholdHC.ArbitraryLawController
