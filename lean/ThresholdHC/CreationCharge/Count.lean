import ThresholdHC.CreationCharge.Specification
import ThresholdHC.Tier5.StoppingBase
import ThresholdHC.Tier6.Full

/-! Created coins are observed and counted by the work.

Along a tape on which every step is observed exactly when the policy selects a
label (`Tier5.realized_creation_valid_step`), every label in `createdLabels` was
selected at an observed earlier step, and the number of distinct labels selected
before step `n` is at most the number of observations before step `n`. -/
noncomputable section
namespace ThresholdHC.CreationCharge
open MeasureTheory Filter ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open scoped ENNReal

/-- Every created label was selected at an earlier step, and that step is observed. -/
theorem createdLabels_observed (pol : List Bool → Option ℕ) (x : ProcessTape)
    (hx : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome) (n : ℕ) :
    ∀ i ∈ createdLabels pol x n,
      ∃ k < n, pol (processHistory x k) = some i ∧ (x k).isSome := by
  intro i hi
  unfold createdLabels at hi
  rw [Finset.mem_biUnion] at hi
  obtain ⟨k, -, hk⟩ := hi
  rw [Option.mem_toFinset] at hk
  refine ⟨k, k.isLt, hk, ?_⟩
  rw [hx k, hk]
  rfl

/-- The number of labels selected before step `n` is at most the number of observed
steps before `n`. -/
theorem createdLabels_card_le (pol : List Bool → Option ℕ) (x : ProcessTape)
    (hx : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome) (n : ℕ) :
    (createdLabels pol x n).card ≤
      (Finset.univ.filter (fun t : Fin n => (x t).isSome = true)).card := by
  unfold createdLabels
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro k _
  rw [Option.card_toFinset]
  cases h : pol (processHistory x k) with
  | none => exact Nat.zero_le _
  | some i =>
    have hk : (x k).isSome = true := by rw [hx k, h]; rfl
    simp [hk]

/-- Created coins are at most the total work along a valid tape. -/
theorem totalCreated_le_of_valid (pol : List Bool → Option ℕ) (x : ProcessTape)
    (hx : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome) :
    totalCreated pol x ≤ totalProcessWork x := by
  unfold totalCreated totalProcessWork
  apply iSup_mono
  intro n
  have h := createdLabels_card_le pol x hx n
  have hw : workOf (processPrefix n x) =
      ((Finset.univ.filter (fun t : Fin n => (x t).isSome = true)).card : ℝ) := rfl
  rw [hw, ENNReal.ofReal_natCast]
  exact_mod_cast h

/-- Almost surely, every step is observed exactly when the policy selects a label. -/
theorem experiment_valid (R : Type) [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    ∀ᵐ z ∂experimentLaw μ A q, ∀ k,
      (z.2 k).isSome = (A.policy z.1.1 (processHistory z.2 k)).isSome := by
  have hr := population_realization R μ A q
  apply ae_all_iff.mpr
  intro n
  have h := realized_creation_valid_step (populationSeedLaw μ A)
    (experimentLaw μ A q) Prod.fst Prod.snd
    (populationPolicy A) populationGap (populationPrior q)
    measurable_fst (fun k b => measurableSet_eq_fun
      ((measurable_pi_apply k).comp measurable_snd) measurable_const)
    (measurable_populationPolicy A) hr.2 n
  simpa only [populationPolicy] using h

theorem createdObserved_holds : CreatedObservedStatement := by
  intro R _ μ _ A q
  filter_upwards [experiment_valid R μ A q] with z hz
  exact ⟨fun n => createdLabels_observed (A.policy z.1.1) z.2 hz n,
    totalCreated_le_of_valid (A.policy z.1.1) z.2 hz⟩

end ThresholdHC.CreationCharge
