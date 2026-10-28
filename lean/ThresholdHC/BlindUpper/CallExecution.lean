import ThresholdHC.BlindUpper.BatchMachine

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier2
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
theorem tapeWord_succ (n : ℕ) (ω : ℕ → Bool) :
    tapeWord (n+1) ω = tapeWord n ω ++ [ω n] := by
  unfold tapeWord
  rw [List.ofFn_succ']
  simp [tapePrefix,List.concat_eq_append]
  rfl

/-- Before the stopping count is reached, every observed flip stays in this call. -/
theorem batchRun_call_partial (L : ℕ) (r : BatchSeed) (c : BatchControl) (j : ℕ)
    (hj : controlLabel c = some j) (ω : ℕ → Bool) (n : ℕ)
    (hn : n < paddedCutoffCost L ((r j).1,ω)) :
    batchRun L r (c,[]) (tapeWord n ω) = (c,tapeWord n ω) := by
  induction n with
  | zero => simp [batchRun,tapeWord]
  | succ n ih =>
    rw [tapeWord_succ,batchRun_append,ih (by omega)]
    change batchStep L r (c,tapeWord n ω) (ω n) = _
    simp only [batchStep,hj]
    rw [← tapeWord_succ,observedCutoffDone_word]
    simp only [show ¬paddedCutoffCost L ((r j).1,ω) ≤ n+1 by omega,decide_false,Bool.false_eq_true,ite_false]

/-- The first completed call changes state exactly once, after its actual cost. -/
theorem batchRun_call_complete (L : ℕ) (r : BatchSeed) (c : BatchControl) (j : ℕ)
    (hj : controlLabel c = some j) (ω : ℕ → Bool) :
    batchRun L r (c,[]) (tapeWord (paddedCutoffCost L ((r j).1,ω)) ω) =
      (controlAdvance L r c (tapeWord (paddedCutoffCost L ((r j).1,ω)) ω),[]) := by
  let N := paddedCutoffCost L ((r j).1,ω)
  have hN : 1 ≤ N := (paddedCutoffCost_bounds L ((r j).1,ω)).1
  have hs : N = (N-1)+1 := by omega
  change batchRun L r (c,[]) (tapeWord N ω) = (controlAdvance L r c (tapeWord N ω),[])
  conv_lhs => rw [hs,tapeWord_succ,batchRun_append]
  rw [batchRun_call_partial L r c j hj ω (N-1) (by omega)]
  change batchStep L r (c,tapeWord (N-1) ω) (ω (N-1)) = _
  simp only [batchStep,hj]
  rw [← tapeWord_succ,← hs,observedCutoffDone_word]
  simp only [show paddedCutoffCost L ((r j).1,ω) ≤ N from le_rfl,decide_true,ite_true]

theorem observedMark_call (L : ℕ) (r : BatchSeed) (j : ℕ) (ω : ℕ → Bool) :
    observedMark L r j (tapeWord (paddedCutoffCost L ((r j).1,ω)) ω) =
      callMark (paddedMark L) (((r j).1,ω),(r j).2) := by
  unfold observedMark callMark paddedMark costParameter uniformCoinFlip paddedRealCost
  simp only [tapeWord_length]
  split_ifs <;> simp_all

theorem observedValue_call (L : ℕ) (r : BatchSeed) (j : ℕ) (ω : ℕ → Bool) :
    cutoffValue L ((r j).1,completeList (tapeWord (paddedCutoffCost L ((r j).1,ω)) ω)) =
      cutoffValue L ((r j).1,ω) :=
  paddedCutoff_observed_value L (r j).1 _ ω le_rfl

end ThresholdHC.BlindUpper
