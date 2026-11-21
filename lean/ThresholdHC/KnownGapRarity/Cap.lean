import ThresholdHC.KnownGapRarity.Estimator
import ThresholdHC.HardBudget.Controller

/-! The deterministic work cap. For calls of constant cost `c`, the plan controller
on `n` labels asks for an observation exactly while fewer than `n c` bits have been
observed, so its policy is `HardBudget.stopAt (n c)` of a reader, and the public
`HardBudget.stopAt_pathwise_cap` bounds the work on every admissible path. The
fixed plan with `n = floor(B/m)` coins and `m` flips each therefore never spends
more than `floor B` flips, and neither does the debiased or clipped estimator,
which share its policy. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.KnownGapRarity
open ThresholdHC.Tier6 ThresholdHC.FixedPlan ThresholdHC.HardBudget
open ThresholdHC.EntropyTailExecution

/-- One call of constant cost `c`, started with a partial word `w`. -/
theorem planRun_const_call (A : ℕ → FiniteCall) (c : ℕ) (hc : ∀ j ω, (A j).cost ω = c)
    (j : ℕ) (js : List ℕ) (done : List (ℕ × List Bool)) (xs : List Bool) :
    ∀ w : List Bool, w.length < c →
    planRun A ⟨j::js, w, done⟩ xs =
      if w.length + xs.length < c then ⟨j::js, w ++ xs, done⟩
      else planRun A ⟨js, [], done ++ [(j, w ++ xs.take (c - w.length))]⟩
        (xs.drop (c - w.length)) := by
  induction xs with
  | nil =>
    intro w hw
    simp [planRun, hw]
  | cons b xs ih =>
    intro w hw
    have hdone : observedDone (A j) (w ++ [b]) = decide (c ≤ w.length + 1) := by
      simp [observedDone, hc]
    change planRun A (planStep A ⟨j::js, w, done⟩ b) xs = _
    simp only [planStep, hdone]
    by_cases h1 : c ≤ w.length + 1
    · have hcw : c - w.length = 1 := by omega
      have h2 : ¬ w.length + (b :: xs).length < c := by simp; omega
      simp only [h1, decide_true, ite_true, h2, ite_false, hcw]
      simp
    · have h2 : (w ++ [b]).length < c := by simp; omega
      have hcw : c - w.length = (c - (w ++ [b]).length) + 1 := by simp; omega
      simp only [h1, decide_false, Bool.false_eq_true, ite_false, hcw]
      rw [ih (w ++ [b]) h2]
      simp only [List.length_append, List.length_cons, List.length_nil, List.take_succ_cons,
        List.drop_succ_cons, List.append_assoc, List.cons_append, List.nil_append]
      have he : w.length + 1 + xs.length < c ↔ w.length + (xs.length + 1) < c := by omega
      simp only [he]

/-- Constant-cost plans: the plan is finished exactly after `|labels| c` bits. -/
theorem planRun_pending_const (A : ℕ → FiniteCall) (c : ℕ) (hc : ∀ j ω, (A j).cost ω = c)
    (hc0 : 0 < c) (ls : List ℕ) :
    ∀ (done : List (ℕ × List Bool)) (xs : List Bool),
    (planRun A ⟨ls, [], done⟩ xs).pending = [] ↔ ls.length * c ≤ xs.length := by
  induction ls with
  | nil =>
    intro done xs
    rw [planRun_absorbs _ _ rfl]
    simp
  | cons j js ih =>
    intro done xs
    rw [planRun_const_call A c hc j js done xs [] hc0]
    simp only [List.length_nil, zero_add, Nat.sub_zero, List.nil_append, List.length_cons,
      add_one_mul]
    split_ifs with h
    · simp only [false_iff]
      omega
    · rw [ih, List.length_drop]
      omega

/-- The fixed plan's policy is `stopAt (n(2k+1))` of a reader. -/
theorem majority_policy_eq (k n : ℕ) (r : Unit) :
    (majorityEstimator k n).policy r =
      stopAt (n*(2*k+1)) (fun xs => ((majorityEstimator k n).policy r xs).getD 0) := by
  funext xs
  have hiff := planRun_pending_const (fun _ => majorityCall k n) (2*k+1) (fun _ _ => rfl)
    (by omega) (List.range n) [] xs
  rw [List.length_range] at hiff
  unfold stopAt
  change (planRun (fun _ => majorityCall k n) (initialPlan (List.range n)) xs).pending.head? =
    if xs.length < n*(2*k+1) then
      some ((planRun (fun _ => majorityCall k n) (initialPlan (List.range n)) xs).pending.head?.getD 0)
    else none
  unfold initialPlan
  split_ifs with h
  · have hne : (planRun (fun _ => majorityCall k n) ⟨List.range n, [], []⟩ xs).pending ≠ [] :=
      fun he => by have := hiff.mp he; omega
    obtain ⟨a, as, ha⟩ := List.exists_cons_of_ne_nil hne
    rw [ha]
    rfl
  · rw [hiff.mpr (by omega)]
    rfl

/-- The fixed plan never spends more than `n(2k+1)` flips. -/
theorem majority_pathwiseCap (k n : ℕ) : PathwiseCap (majorityEstimator k n) (n*(2*k+1)) :=
  stopAt_pathwise_cap _ _ _ (majority_policy_eq k n)

theorem pathwiseCap_mono {R : Type} [MeasurableSpace R] {A : AdaptiveEstimator R} {N N' : ℕ}
    (h : PathwiseCap A N) (hN : N ≤ N') : PathwiseCap A N' :=
  fun r x hx => (h r x hx).trans (by exact_mod_cast hN)

theorem rawEstimator_pathwiseCap (d : Gap) {B : ℝ} (hB : 0 ≤ B) :
    PathwiseCap (rawEstimator d B) ⌊B⌋₊ := by
  by_cases h : 2 * (flipCount d B : ℝ) ≤ B
  · rw [rawEstimator_of_le h]
    exact pathwiseCap_mono (majority_pathwiseCap _ _) (work_le_floor d hB)
  · rw [rawEstimator_of_lt (lt_of_not_ge h)]
    exact pathwiseCap_mono (majority_pathwiseCap _ _) (by simp)

/-- The known-gap estimator never spends more than `floor B` flips. -/
theorem knownGap_pathwiseCap (d : Gap) {B : ℝ} (hB : 0 ≤ B) :
    PathwiseCap (knownGapEstimator d B) ⌊B⌋₊ :=
  rawEstimator_pathwiseCap d hB

end ThresholdHC.KnownGapRarity
