import ThresholdHC.BlindUpper.PhasePlan

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open scoped ENNReal
theorem phaseLabels_nodup (phase n : ℕ) : (phaseLabels phase n).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  exact Fin.ext (Nat.pair_eq_pair.mp h).2

theorem phaseLabels_disjoint (p q n m : ℕ) (hpq : p ≠ q) :
    List.Disjoint (phaseLabels p n) (phaseLabels q m) := by
  apply List.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hy
  exact hpq (Nat.pair_eq_pair.mp (hi.trans hj.symm)).1

theorem fullBatchLabels_nodup (a b : ℕ) : (fullBatchLabels a b).Nodup := by
  apply List.Nodup.append
  · exact (phaseLabels_nodup 0 (a+1)).append (phaseLabels_nodup 1 (b+1))
      (phaseLabels_disjoint 0 1 _ _ (by omega))
  · exact phaseLabels_nodup 2 (a+b+1)
  · apply List.disjoint_left.mpr
    intro x hx hy
    rcases List.mem_append.mp hx with hx | hx
    · exact (List.disjoint_left.mp (phaseLabels_disjoint 0 2 _ _ (by omega))) hx hy
    · exact (List.disjoint_left.mp (phaseLabels_disjoint 1 2 _ _ (by omega))) hx hy

theorem callWords_append (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (xs ys : List ℕ) :
    callWords L r s (xs++ys) = callWords L r s xs ++ callWords L r s ys := by
  simp [callWords]

theorem callWords_fullBatchLabels (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ) :
    callWords L r s (fullBatchLabels a b) = fullBatchWord L r s a b := by
  simp only [fullBatchLabels,callWords_append,callWords_phaseLabels,fullBatchWord]

/-- On every pair of terminating pilots, the actual population simulation
is exactly the finite concatenation used by the controller. -/
theorem batch_populationPath_eq (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    populationPath (batchPolicy L r) s = fun n => (fullBatchWord L r s a b)[n]? := by
  have h := (fullBatch_plan L r s a b ha hb).path_eq (fullBatchLabels_nodup a b) rfl
  rw [callWords_fullBatchLabels] at h
  exact h

end ThresholdHC.BlindUpper
