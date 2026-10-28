import ThresholdHC.BlindUpper.BatchPath
import ThresholdHC.BlindUpper.ControllerOutput

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open scoped ENNReal
open ThresholdHC.Proofs
open scoped ENNReal

theorem processHistory_word (xs : List Bool) :
    processHistory (fun n => xs[n]?) xs.length = xs := by
  change (List.ofFn (fun i : Fin xs.length => xs[i.val]?)).filterMap id = xs
  have he : (fun i : Fin xs.length => xs[i.val]?) = fun i : Fin xs.length => some xs[i.val] := by
    funext i
    exact List.getElem?_eq_getElem i.isLt
  rw [he, List.ofFn_getElem_eq_map]
  simp

theorem prefix_work_word (xs : List Bool) (n : ℕ) :
    workOf (processPrefix n (fun k => xs[k]?)) = (min n xs.length : ℕ) := by
  induction n with
  | zero => simp [workOf]
  | succ n ih =>
    rw [processPrefix_snoc,workOf_snoc,ih]
    by_cases hn : n < xs.length
    · simp only [List.getElem?_eq_getElem hn,Option.isSome_some,ite_true]
      norm_cast
      omega
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)]
      simp only [Option.isSome_none,Bool.false_eq_true,ite_false,add_zero]
      congr 1
      omega

theorem totalProcessWork_word (xs : List Bool) :
    totalProcessWork (fun n => xs[n]?) = (xs.length : ℝ≥0∞) := by
  unfold totalProcessWork
  simp_rw [prefix_work_word,ENNReal.ofReal_natCast]
  apply le_antisymm
  · apply iSup_le
    intro n
    exact_mod_cast min_le_right n xs.length
  · exact le_iSup_of_le xs.length (by simp)

theorem batch_population_output (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    batchOutput L (r,populationPath (batchPolicy L r) s) = cutoffBatchOutput L (batchInput (r,s)) := by
  rw [batch_populationPath_eq L r s a b ha hb]
  have hh : batchPolicy L r
      (processHistory (fun n => (fullBatchWord L r s a b)[n]?) (fullBatchWord L r s a b).length) = none := by
    rw [processHistory_word]
    change controlLabel (batchRun L r batchInitial (fullBatchWord L r s a b)).1 = none
    rw [run_full_batch L r s a b ha hb]
    rfl
  rw [batchOutput_at_halt L r _ _ hh,processHistory_word]
  exact fullBatch_controller_output L r s a b ha hb

theorem phaseWord_length (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) :
    (phaseWord L r s phase n).length =
      ∑ i ∈ Finset.range n, paddedCutoffCost L ((r (Nat.pair phase i)).1,s (Nat.pair phase i)) := by
  induction n with
  | zero => simp [phaseWord,phaseWords]
  | succ n ih =>
    rw [phaseWord_succ,List.length_append,ih,Finset.sum_range_succ]
    simp [batchCallWord,tapeWord]

theorem phase_pilot_work (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase a : ℕ)
    (ha : firstSuccess (phaseMark L r s phase) = a) :
    firstPilotWork (paddedMark L) (fun x => ENNReal.ofReal (paddedRealCost L x))
        (fun i => seededMarkedCalls (r,s) (Nat.pair phase i)) =
      ((phaseWord L r s phase (a+1)).length : ℝ≥0∞) := by
  rw [firstPilotWork_of_stop _ _ _ a ha,phaseWord_length]
  simp [paddedRealCost,seededMarkedCalls,Nat.cast_sum]

theorem phase_production_work (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (f : ℕ) :
    ENNReal.ofReal (productionCost (paddedRealCost L) f (batchInput (r,s)).2) =
      ((phaseWord L r s 2 (f+1)).length : ℝ≥0∞) := by
  unfold productionCost
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => (paddedRealCost_bounds L _).1)]
  simp only [paddedRealCost,ENNReal.ofReal_natCast,batchInput,threeMarkedStreams,
    seededMarkedCalls,Function.comp_apply,phaseWord_length,Nat.cast_sum]
  simpa using (Fin.sum_univ_eq_sum_range
    (fun i => (paddedCutoffCost L ((r (Nat.pair 2 i)).1,s (Nat.pair 2 i)) : ℝ≥0∞)) (f+1))

theorem fullBatch_work (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    ((fullBatchWord L r s a b).length : ℝ≥0∞) = cutoffBatchWork L (batchInput (r,s)) := by
  unfold cutoffBatchWork calibrationWork twoPilotWork
  rw [twoPilotFailures_phase L r s a b ha hb,phase_production_work]
  change _ = firstPilotWork _ _ (fun i => seededMarkedCalls (r,s) (Nat.pair 0 i)) +
    firstPilotWork _ _ (fun i => seededMarkedCalls (r,s) (Nat.pair 1 i)) + _
  rw [phase_pilot_work L r s 0 a ha,phase_pilot_work L r s 1 b hb]
  simp [fullBatchWord,Nat.cast_add,add_assoc]

theorem batch_population_work (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    totalProcessWork (populationPath (batchPolicy L r) s) = cutoffBatchWork L (batchInput (r,s)) := by
  rw [batch_populationPath_eq L r s a b ha hb,totalProcessWork_word,fullBatch_work L r s a b ha hb]

end ThresholdHC.BlindUpper
