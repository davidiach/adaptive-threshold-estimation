import ThresholdHC.BlindUpper.ControllerExecution

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3
open scoped ENNReal

theorem phaseWords_get (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) (i : Fin n) :
    (phaseWords L r s phase n)[i.val]'(by simp) = batchCallWord L r s (Nat.pair phase i.val) := by
  simp [phaseWords]

theorem controlOutput_production (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (f : ℕ) :
    controlOutput L r (.stopped (phaseWords L r s 2 (f+1))) =
      productionAverage (cutoffValue L) f (batchInput (r,s)).2 := by
  simp only [controlOutput,phaseWords_length]
  have hval (i : ℕ) (hi : i < (phaseWords L r s 2 (f+1)).length) :
      cutoffValue L ((r (Nat.pair 2 i)).1,
        completeList (phaseWords L r s 2 (f+1))[i]) =
      cutoffValue L ((r (Nat.pair 2 i)).1,s (Nat.pair 2 i)) := by
    rw [phaseWords_get L r s 2 (f+1) ⟨i,by simpa using hi⟩]
    exact observedValue_call L r (Nat.pair 2 i) (s (Nat.pair 2 i))
  simp_rw [hval]
  have hsum : (∑ i : Fin (phaseWords L r s 2 (f+1)).length,
      cutoffValue L ((r (Nat.pair 2 i.val)).1,s (Nat.pair 2 i.val))) =
      ∑ i : Fin (f+1), cutoffValue L ((r (Nat.pair 2 i.val)).1,s (Nat.pair 2 i.val)) :=
    Fintype.sum_equiv (finCongr (phaseWords_length L r s 2 (f+1))) _ _ (by intro i; rfl)
  rw [hsum]
  unfold productionAverage finiteAverage productionPrefix batchInput threeMarkedStreams seededMarkedCalls
  simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one]
  ring

theorem twoPilotFailures_phase (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    twoPilotFailures (paddedMark L) (batchInput (r,s)).1 = a+b := by
  change (firstSuccess (phaseMark L r s 0)).toNat+(firstSuccess (phaseMark L r s 1)).toNat = _
  rw [ha,hb]
  rfl

/-- The terminal controller value is exactly the estimator used in the
calibration calculation whenever the two pilots finish. -/
theorem fullBatch_controller_output (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    controlOutput L r (batchRun L r batchInitial (fullBatchWord L r s a b)).1 =
      cutoffBatchOutput L (batchInput (r,s)) := by
  rw [run_full_batch L r s a b ha hb]
  change controlOutput L r (.stopped (phaseWords L r s 2 (a+b+1))) = _
  rw [controlOutput_production]
  change _ = productionAverage (cutoffValue L)
    (twoPilotFailures (paddedMark L) (batchInput (r,s)).1) (batchInput (r,s)).2
  rw [twoPilotFailures_phase L r s a b ha hb]

end ThresholdHC.BlindUpper
