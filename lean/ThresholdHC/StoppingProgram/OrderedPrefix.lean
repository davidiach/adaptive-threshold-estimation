import ThresholdHC.StoppingProgram.WordFlow
import ThresholdHC.CriticalEntropy.RepeatedSignModel

/-! Prefix conservation for an arbitrary seeded, order-dependent capped
stopping procedure. No count-sufficiency restriction is imposed on the rule. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy

def completedStop {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) (r : R) : ℕ :=
  (A.stop (r,completePrefix n w)).toNat

theorem measurable_completedStop {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) : Measurable (completedStop A w) :=
  (measurable_of_countable ENat.toNat).comp
    (A.measurable_stop.comp (measurable_id.prodMk measurable_const))

theorem completedStop_le_cap {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {N n : ℕ} (hcap : ∀ z, A.stop z ≤ N) (w : Fin n → Bool) (r : R) :
    completedStop A w r ≤ N := by
  exact ENat.toNat_le_toNat (hcap _) (by simp)

theorem completedStop_eq_iff {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {N n : ℕ} (hcap : ∀ z, A.stop z ≤ N) (w : Fin n → Bool) (r : R) :
    completedStop A w r = n ↔ (r,w) ∈ A.stopPrefix n := by
  have hfin : A.stop (r,completePrefix n w) ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hcap _)
  have he := A.stop_observable n (r,completePrefix n w)
  simp only [tapePrefix_completePrefix] at he
  rw [he]
  constructor
  · intro h
    rw [← ENat.natCast_toNat hfin]
    exact congrArg (fun k : ℕ => (k:ℕ∞)) h
  · intro h
    simp [completedStop,h]

theorem completedStop_snoc_le_iff {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {N n : ℕ} (hcap : ∀ z, A.stop z ≤ N)
    (w : Fin n → Bool) (b : Bool) (r : R) :
    completedStop A (Fin.snoc w b) r ≤ n ↔ completedStop A w r ≤ n := by
  have hfin (ω : ℕ → Bool) : A.stop (r,ω) ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hcap _)
  have hp : Tier2.tapePrefix n (completePrefix (n+1) (Fin.snoc w b)) =
      Tier2.tapePrefix n (completePrefix n w) := by
    rw [tapePrefix_completePrefix]
    funext i
    change (if h : i.val < n+1 then Fin.snoc (α := fun _ : Fin (n+1) => Bool) w b ⟨i.val,h⟩ else false) = w i
    rw [dite_eq_left (by omega)]
    change Fin.snoc (α := fun _ : Fin (n+1) => Bool) w b i.castSucc = w i
    rw [Fin.snoc_castSucc]
  have hcast (ω : ℕ → Bool) : ((A.stop (r,ω)).toNat:ℕ∞) = A.stop (r,ω) := ENat.natCast_toNat (hfin ω)
  constructor
  · intro h
    have hc : A.stop (r,completePrefix (n+1) (Fin.snoc w b)) ≤ n := by
      rw [← hcast]
      exact_mod_cast h
    have hs := (stopped_before_prefix_ext A r _ _ n hp hc).1
    have he := congrArg ENat.toNat hs
    change completedStop A w r = completedStop A (Fin.snoc w b) r at he
    exact he.le.trans h
  · intro h
    have hc : A.stop (r,completePrefix n w) ≤ n := by
      rw [← hcast]
      exact_mod_cast h
    have hs := (stopped_before_prefix_ext A r _ _ n hp.symm hc).1
    have he := congrArg ENat.toNat hs
    change completedStop A (Fin.snoc w b) r = completedStop A w r at he
    exact he.le.trans h

def orderedStopIndicator {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) (r : R) : ℝ :=
  if 0 < n ∧ completedStop A w r = n then 1 else 0

def orderedContinueIndicator {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) (r : R) : ℝ :=
  if n < completedStop A w r then 1 else 0

theorem ordered_indicator_bounds {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) (r : R) :
    0 ≤ orderedStopIndicator A w r ∧ orderedStopIndicator A w r ≤ 1 ∧
    0 ≤ orderedContinueIndicator A w r ∧ orderedContinueIndicator A w r ≤ 1 := by
  unfold orderedStopIndicator orderedContinueIndicator
  split_ifs <;> norm_num

theorem measurable_orderedStopIndicator {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) : Measurable (orderedStopIndicator A w) := by
  unfold orderedStopIndicator
  by_cases hn : 0 < n
  · simp only [hn,true_and]
    exact measurable_const.ite (measurableSet_eq_fun (measurable_completedStop A w) measurable_const) measurable_const
  · simp only [hn,false_and,ite_false]
    exact measurable_const

theorem measurable_orderedContinueIndicator {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) : Measurable (orderedContinueIndicator A w) := by
  unfold orderedContinueIndicator
  exact measurable_const.ite (measurableSet_lt measurable_const (measurable_completedStop A w)) measurable_const

theorem ordered_indicator_conservation {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {N n : ℕ} (hcap : ∀ z, A.stop z ≤ N)
    (w : Fin n → Bool) (b : Bool) (r : R) :
    orderedStopIndicator A (Fin.snoc w b) r+orderedContinueIndicator A (Fin.snoc w b) r =
      orderedContinueIndicator A w r := by
  have he := completedStop_snoc_le_iff A hcap w b r
  unfold orderedStopIndicator orderedContinueIndicator
  simp only [Nat.succ_pos,true_and]
  split_ifs <;> norm_num <;> omega

theorem ordered_indicator_terminal {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {N : ℕ} (hcap : ∀ z, A.stop z ≤ N) (w : Fin N → Bool) (r : R) :
    orderedContinueIndicator A w r = 0 := by
  exact ite_eq_right (not_lt.mpr (completedStop_le_cap A hcap w r))

end ThresholdHC.StoppingProgram
