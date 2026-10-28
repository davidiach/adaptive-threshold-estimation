import ThresholdHC.BlindUpper.MachinePath

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open scoped ENNReal
theorem updated_tape_advance (s : ℕ → ℕ → Bool) (j n : ℕ) :
    Function.update (Function.update s j (tapeDrop n (s j))) j
      (tapeDrop 1 (Function.update s j (tapeDrop n (s j)) j)) =
        Function.update s j (tapeDrop (n+1) (s j)) := by
  rw [Function.update_self,Function.update_idem]
  congr 1
  funext k
  simp only [tapeDrop]
  congr 1
  omega

/-- Prefix execution charges exactly the revealed flips to the active label. -/
theorem consumes_call_prefix (L : ℕ) (r : BatchSeed) (c : BatchControl) (s : ℕ → ℕ → Bool)
    (j : ℕ) (hj : controlLabel c = some j) (n : ℕ)
    (hn : n ≤ paddedCutoffCost L ((r j).1,s j)) :
    BatchConsumes L r (c,[]) s (tapeWord n (s j))
      (batchRun L r (c,[]) (tapeWord n (s j))) (Function.update s j (tapeDrop n (s j))) := by
  induction n with
  | zero =>
    have hd : tapeDrop 0 (s j) = s j := by funext k; simp [tapeDrop]
    simp only [hd,Function.update_eq_self,tapeWord,List.ofFn_zero,batchRun,List.foldl_nil]
    exact .nil _ _
  | succ n ih =>
    have hprev := ih (by omega)
    have hs := batchRun_call_partial L r c j hj (s j) n (by omega)
    rw [hs] at hprev
    have hsingle : BatchConsumes L r (c,tapeWord n (s j))
        (Function.update s j (tapeDrop n (s j))) [s j n]
        (batchStep L r (c,tapeWord n (s j)) (s j n))
        (Function.update s j (tapeDrop (n+1) (s j))) := by
      rw [← updated_tape_advance]
      exact .cons hj (by simp [tapeDrop]) (.nil _ _)
    have h := hprev.append hsingle
    rw [← tapeWord_succ] at h
    convert h using 1
    rw [tapeWord_succ,batchRun_append,hs]
    rfl

theorem consumes_call (L : ℕ) (r : BatchSeed) (c : BatchControl) (s : ℕ → ℕ → Bool)
    (j : ℕ) (hj : controlLabel c = some j) :
    BatchConsumes L r (c,[]) s (batchCallWord L r s j)
      (controlAdvance L r c (batchCallWord L r s j),[])
      (Function.update s j (tapeDrop (paddedCutoffCost L ((r j).1,s j)) (s j))) := by
  have h := consumes_call_prefix L r c s j hj (paddedCutoffCost L ((r j).1,s j)) le_rfl
  rw [batchRun_call_complete L r c j hj] at h
  exact h

end ThresholdHC.BlindUpper
