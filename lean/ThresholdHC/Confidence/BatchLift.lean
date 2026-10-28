import ThresholdHC.Confidence.Execution

noncomputable section
set_option maxHeartbeats 1200000
namespace ThresholdHC.Confidence
open ThresholdHC.Tier3 ThresholdHC.BlindUpper ThresholdHC.CriticalEntropy

theorem pair_ne_of_index_ne {m : ℕ} {i k : MedianIndex m} (hki : k ≠ i) (j l : ℕ) :
    Nat.pair k.val j ≠ Nat.pair i.val l := by
  intro he
  exact hki (Fin.ext (Nat.pair_eq_pair.mp he).1)

/-- Lifting a inner finite execution changes only that repetition's controller
and pair-labelled tapes. Earlier repetitions must already have stopped. -/
theorem lift_batch_consumes {m L : ℕ} {r : RepeatSeed} (i : MedianIndex m)
    {st st' : BatchMachineState} {inner inner' : ℕ → ℕ → Bool} {xs : List Bool}
    (h : BatchConsumes L (r i.val) st inner xs st' inner') :
    ∀ (s : RepeatState m) (t : ℕ → ℕ → Bool), s i = st →
      (∀ j, t (Nat.pair i.val j) = inner j) →
      (∀ k : MedianIndex m, k < i → controlLabel (s k).1 = none) →
      ∃ u, RepeatConsumes m L r s t xs (Function.update s i st') u ∧
        ∀ k : MedianIndex m, k ≠ i → ∀ j, u (Nat.pair k.val j) = t (Nat.pair k.val j) := by
  induction h with
  | nil st inner =>
    intro s t hsi hlocal hp
    refine ⟨t, ?_, fun _ _ _ => rfl⟩
    rw [← hsi, Function.update_eq_self]
    exact .nil _ _
  | @cons st st' inner inner' j b xs ha hb rest ih =>
    intro s t hsi hlocal hp
    let s1 := Function.update s i (batchStep L (r i.val) st b)
    let t1 := Function.update t (Nat.pair i.val j) (tapeDrop 1 (t (Nat.pair i.val j)))
    have hs1 : s1 i = batchStep L (r i.val) st b := Function.update_self _ _ _
    have ht1 : ∀ k, t1 (Nat.pair i.val k) =
        Function.update inner j (tapeDrop 1 (inner j)) k := by
      intro k
      by_cases hkj : k = j
      · subst k
        simp only [t1,Function.update_self,hlocal]
      · have hpair : Nat.pair i.val k ≠ Nat.pair i.val j := by
          intro he
          exact hkj (Nat.pair_eq_pair.mp he).2
        simp only [t1,Function.update_of_ne hpair,Function.update_of_ne hkj,hlocal]
    have hp1 : ∀ k : MedianIndex m, k < i → controlLabel (s1 k).1 = none := by
      intro k hk
      simpa only [s1,Function.update_of_ne (ne_of_lt hk)] using hp k hk
    obtain ⟨u,hu,hfresh⟩ := ih s1 t1 hs1 ht1 hp1
    have hai : controlLabel (s i).1 = some j := by rw [hsi]; exact ha
    have hselect := selectActive_first s i (by rw [hai]; simp) hp
    have hstep : repeatStep m L r s b = s1 := by simp only [repeatStep,hselect,s1,hsi]
    have hu' : RepeatConsumes m L r s1 t1 xs (Function.update s i st') u := by
      simpa only [s1,Function.update_idem] using hu
    refine ⟨u, ?_, ?_⟩
    · apply RepeatConsumes.cons (repeatLabel_first s i j hai hp)
        (show t (Nat.pair i.val j) 0 = b by rw [hlocal]; exact hb)
      rw [hstep]
      exact hu'
    · intro k hki l
      rw [hfresh k hki l]
      exact Function.update_of_ne (pair_ne_of_index_ne hki l j) _ _

end ThresholdHC.Confidence
