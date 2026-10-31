import ThresholdHC.EntropyTailExecution.PlanExecution
import ThresholdHC.BlindUpper.ActualBatch

/-! Exact cost and output identities for the observable finite-plan estimator
in the original population experiment. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

def plannedCost (A : ℕ → FiniteCall) (labels : List ℕ) (s : ℕ → ℕ → Bool) : ℕ :=
  (labels.map (fun j => (A j).cost (s j))).sum

def plannedValue (A : ℕ → FiniteCall) (labels : List ℕ) (s : ℕ → ℕ → Bool) : ℝ :=
  (labels.map (fun j => (A j).value (s j))).sum

theorem planWord_length (A : ℕ → FiniteCall) (labels : List ℕ) (s : ℕ → ℕ → Bool) :
    (planWord A s labels).length = plannedCost A labels s := by
  induction labels with
  | nil => rfl
  | cons j js ih =>
    simp only [planWord, List.flatMap_cons, List.length_append, callWord, tapeWord_length,
      plannedCost, List.map_cons, List.sum_cons] at ih ⊢
    exact congrArg (fun n => (A j).cost (s j)+n) ih

theorem planRecords_output (A : ℕ → FiniteCall) (labels : List ℕ) (s : ℕ → ℕ → Bool) :
    planStateOutput A ⟨[], [], planRecords A s labels⟩ = plannedValue A labels s := by
  simp only [planStateOutput, planRecords, List.map_map, Function.comp_def, callWord,
    observedValue_word, plannedValue]

theorem finitePlanOutput_at_halt {R : Type} (A : ℕ → FiniteCall) (plan : R → List ℕ)
    (r : R) (x : ProcessTape) (n : ℕ) (hn : finitePlanPolicy A plan r (processHistory x n) = none) :
    finitePlanOutput A plan (r,x) =
      planStateOutput A (planRun A (initialPlan (plan r)) (processHistory x n)) := by
  have hmark : (finitePlanPolicy A plan r (processHistory x n)).isNone = true := by rw [hn]; rfl
  obtain ⟨k,hkn,hk⟩ := firstSuccess_finite_le
    (fun j => (finitePlanPolicy A plan r (processHistory x j)).isNone) n hmark
  have hkstop : finitePlanPolicy A plan r (processHistory x k) = none :=
    Option.isNone_iff_eq_none.mp ((firstSuccess_eq _ _).mp hk).1
  have he : planRun A (initialPlan (plan r)) (processHistory x n) =
      planRun A (initialPlan (plan r)) (processHistory x k) := by
    conv_lhs => rw [show n = k+(n-k) by omega, processHistory_add, planRun_append]
    exact planRun_absorbs A _ hkstop _
  change planStateOutput A (planRun A (initialPlan (plan r))
    (processHistory x (finitePlanHaltTime A plan (r,x)).toNat)) = _
  rw [show finitePlanHaltTime A plan (r,x) = k from hk]
  simp only [ENat.toNat_natCast]
  rw [he]

theorem finitePlan_population_output {R : Type} (A : ℕ → FiniteCall) (plan : R → List ℕ)
    (r : R) (s : ℕ → ℕ → Bool) (hn : (plan r).Nodup) :
    finitePlanOutput A plan (r,populationPath (finitePlanPolicy A plan r) s) = plannedValue A (plan r) s := by
  have hp := finitePlan_path_eq A s (plan r) hn
  change populationPath (finitePlanPolicy A plan r) s = _ at hp
  rw [hp]
  obtain ⟨t,ht⟩ := full_plan_consumes A s (plan r) hn [] s (fun _ _ => rfl)
  have hs := ht.state_eq
  simp only [List.nil_append] at hs
  have hh : finitePlanPolicy A plan r
      (processHistory (fun n => (planWord A s (plan r))[n]?) (planWord A s (plan r)).length) = none := by
    rw [processHistory_word]
    change planLabel (planRun A ⟨plan r, [], []⟩ (planWord A s (plan r))) = none
    rw [hs]
    rfl
  rw [finitePlanOutput_at_halt A plan r _ _ hh, processHistory_word]
  change planStateOutput A (planRun A ⟨plan r, [], []⟩ (planWord A s (plan r))) = _
  rw [hs, planRecords_output]

theorem finitePlan_population_work {R : Type} (A : ℕ → FiniteCall) (plan : R → List ℕ)
    (r : R) (s : ℕ → ℕ → Bool) (hn : (plan r).Nodup) :
    totalProcessWork (populationPath (finitePlanPolicy A plan r) s) = (plannedCost A (plan r) s : ℝ≥0∞) := by
  have hp := finitePlan_path_eq A s (plan r) hn
  change populationPath (finitePlanPolicy A plan r) s = _ at hp
  rw [hp, totalProcessWork_word, planWord_length]

variable {R : Type} [Countable R] [MeasurableSpace R] [MeasurableSingletonClass R]

theorem finitePlan_expectedWork (ν : Measure R) [IsProbabilityMeasure ν]
    (A : ℕ → FiniteCall) (plan : R → List ℕ) (hn : ∀ r, (plan r).Nodup)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    expectedWork μ (finitePlanEstimator ν A plan) q =
      ∫⁻ z : R × (ℕ → ℕ → Bool), (plannedCost A (plan z.1) z.2 : ℝ≥0∞)
        ∂ν.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) := by
  rw [original_expectedWork_simulation]
  apply lintegral_congr
  intro z
  exact finitePlan_population_work A plan z.1 z.2 (hn z.1)

theorem finitePlan_squaredRisk (ν : Measure R) [IsProbabilityMeasure ν]
    (A : ℕ → FiniteCall) (plan : R → List ℕ) (hn : ∀ r, (plan r).Nodup)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ) :
    squaredRisk (experimentLaw μ (finitePlanEstimator ν A plan) q)
      (populationOutput (finitePlanEstimator ν A plan)) a =
      ∫⁻ z : R × (ℕ → ℕ → Bool), ENNReal.ofReal ((plannedValue A (plan z.1) z.2-a)^2)
        ∂ν.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) := by
  rw [original_squaredRisk_simulation]
  apply lintegral_congr
  intro z
  change ENNReal.ofReal ((finitePlanOutput A plan (z.1,populationPath (finitePlanPolicy A plan z.1) z.2)-a)^2) = _
  rw [finitePlan_population_output A plan z.1 z.2 (hn z.1)]

end ThresholdHC.EntropyTailExecution
