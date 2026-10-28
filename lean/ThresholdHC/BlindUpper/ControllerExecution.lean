import ThresholdHC.BlindUpper.CallExecution
import ThresholdHC.BlindUpper.TerminalOutput

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier2
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
def batchCallWord (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (j : ℕ) : List Bool :=
  tapeWord (paddedCutoffCost L ((r j).1,s j)) (s j)

def phaseWords (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) : List (List Bool) :=
  List.ofFn (fun i : Fin n => batchCallWord L r s (Nat.pair phase i.val))

def phaseWord (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) : List Bool :=
  (phaseWords L r s phase n).flatten

@[simp] theorem phaseWords_length (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) :
    (phaseWords L r s phase n).length = n := List.length_ofFn

theorem phaseWords_succ (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) :
    phaseWords L r s phase (n+1) = phaseWords L r s phase n ++ [batchCallWord L r s (Nat.pair phase n)] := by
  unfold phaseWords
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

theorem phaseWord_succ (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) :
    phaseWord L r s phase (n+1) = phaseWord L r s phase n ++ batchCallWord L r s (Nat.pair phase n) := by
  simp [phaseWord,phaseWords_succ]

def phaseMark (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase i : ℕ) : Bool :=
  callMark (paddedMark L) (seededMarkedCalls (r,s) (Nat.pair phase i))

theorem observedMark_phaseWord (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase i : ℕ) :
    observedMark L r (Nat.pair phase i) (batchCallWord L r s (Nat.pair phase i)) =
      phaseMark L r s phase i := observedMark_call L r (Nat.pair phase i) (s (Nat.pair phase i))

theorem run_first_pilot_prefix (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (n : ℕ)
    (h : ∀ i < n, phaseMark L r s 0 i = false) :
    batchRun L r batchInitial (phaseWord L r s 0 n) = (.pilotOne n,[]) := by
  induction n with
  | zero => simp [batchRun,batchInitial,phaseWord,phaseWords]
  | succ n ih =>
    rw [phaseWord_succ,batchRun_append,ih (fun i hi => h i (by omega))]
    rw [show batchCallWord L r s (Nat.pair 0 n) =
      tapeWord (paddedCutoffCost L ((r (Nat.pair 0 n)).1,s (Nat.pair 0 n))) (s (Nat.pair 0 n)) from rfl,
      batchRun_call_complete L r (.pilotOne n) (Nat.pair 0 n) rfl]
    change (controlAdvance L r (.pilotOne n) (batchCallWord L r s (Nat.pair 0 n)),[]) = _
    simp only [controlAdvance,observedMark_phaseWord,h n (by omega),Bool.false_eq_true,ite_false]

theorem run_first_pilot (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a : ℕ)
    (h : firstSuccess (phaseMark L r s 0) = a) :
    batchRun L r batchInitial (phaseWord L r s 0 (a+1)) = (.pilotTwo a 0,[]) := by
  obtain ⟨ht,hf⟩ := (firstSuccess_eq _ _).mp h
  rw [phaseWord_succ,batchRun_append,run_first_pilot_prefix L r s a hf]
  rw [show batchCallWord L r s (Nat.pair 0 a) =
    tapeWord (paddedCutoffCost L ((r (Nat.pair 0 a)).1,s (Nat.pair 0 a))) (s (Nat.pair 0 a)) from rfl,
    batchRun_call_complete L r (.pilotOne a) (Nat.pair 0 a) rfl]
  change (controlAdvance L r (.pilotOne a) (batchCallWord L r s (Nat.pair 0 a)),[]) = _
  simp only [controlAdvance,observedMark_phaseWord,ht,ite_true]

theorem run_second_pilot_prefix (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a n : ℕ)
    (h : ∀ i < n, phaseMark L r s 1 i = false) :
    batchRun L r (.pilotTwo a 0,[]) (phaseWord L r s 1 n) = (.pilotTwo a n,[]) := by
  induction n with
  | zero => simp [batchRun,phaseWord,phaseWords]
  | succ n ih =>
    rw [phaseWord_succ,batchRun_append,ih (fun i hi => h i (by omega))]
    rw [show batchCallWord L r s (Nat.pair 1 n) =
      tapeWord (paddedCutoffCost L ((r (Nat.pair 1 n)).1,s (Nat.pair 1 n))) (s (Nat.pair 1 n)) from rfl,
      batchRun_call_complete L r (.pilotTwo a n) (Nat.pair 1 n) rfl]
    change (controlAdvance L r (.pilotTwo a n) (batchCallWord L r s (Nat.pair 1 n)),[]) = _
    simp only [controlAdvance,observedMark_phaseWord,h n (by omega),Bool.false_eq_true,ite_false]

theorem run_second_pilot (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (h : firstSuccess (phaseMark L r s 1) = b) :
    batchRun L r (.pilotTwo a 0,[]) (phaseWord L r s 1 (b+1)) = (.production (a+b) [],[]) := by
  obtain ⟨ht,hf⟩ := (firstSuccess_eq _ _).mp h
  rw [phaseWord_succ,batchRun_append,run_second_pilot_prefix L r s a b hf]
  rw [show batchCallWord L r s (Nat.pair 1 b) =
    tapeWord (paddedCutoffCost L ((r (Nat.pair 1 b)).1,s (Nat.pair 1 b))) (s (Nat.pair 1 b)) from rfl,
    batchRun_call_complete L r (.pilotTwo a b) (Nat.pair 1 b) rfl]
  change (controlAdvance L r (.pilotTwo a b) (batchCallWord L r s (Nat.pair 1 b)),[]) = _
  simp only [controlAdvance,observedMark_phaseWord,ht,ite_true]

theorem run_production_prefix (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (f n : ℕ) (hn : n ≤ f) :
    batchRun L r (.production f [],[]) (phaseWord L r s 2 n) = (.production f (phaseWords L r s 2 n),[]) := by
  induction n with
  | zero => simp [batchRun,phaseWord,phaseWords]
  | succ n ih =>
    rw [phaseWord_succ,batchRun_append,ih (by omega)]
    rw [show batchCallWord L r s (Nat.pair 2 n) =
      tapeWord (paddedCutoffCost L ((r (Nat.pair 2 n)).1,s (Nat.pair 2 n))) (s (Nat.pair 2 n)) from rfl,
      batchRun_call_complete L r (.production f (phaseWords L r s 2 n)) (Nat.pair 2 n)
        (by simp [controlLabel])]
    change (controlAdvance L r (.production f (phaseWords L r s 2 n))
      (batchCallWord L r s (Nat.pair 2 n)),[]) = _
    simp only [controlAdvance,phaseWords_length,show n ≠ f by omega,ite_false,phaseWords_succ]

theorem run_production (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (f : ℕ) :
    batchRun L r (.production f [],[]) (phaseWord L r s 2 (f+1)) =
      (.stopped (phaseWords L r s 2 (f+1)),[]) := by
  rw [phaseWord_succ,batchRun_append,run_production_prefix L r s f f le_rfl]
  rw [show batchCallWord L r s (Nat.pair 2 f) =
    tapeWord (paddedCutoffCost L ((r (Nat.pair 2 f)).1,s (Nat.pair 2 f))) (s (Nat.pair 2 f)) from rfl,
    batchRun_call_complete L r (.production f (phaseWords L r s 2 f)) (Nat.pair 2 f)
      (by simp [controlLabel])]
  change (controlAdvance L r (.production f (phaseWords L r s 2 f))
    (batchCallWord L r s (Nat.pair 2 f)),[]) = _
  simp only [controlAdvance,phaseWords_length,ite_true,phaseWords_succ]

def fullBatchWord (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ) : List Bool :=
  phaseWord L r s 0 (a+1) ++ phaseWord L r s 1 (b+1) ++ phaseWord L r s 2 (a+b+1)

theorem run_full_batch (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    batchRun L r batchInitial (fullBatchWord L r s a b) =
      (.stopped (phaseWords L r s 2 (a+b+1)),[]) := by
  simp only [fullBatchWord,batchRun_append,run_first_pilot L r s a ha,
    run_second_pilot L r s a b hb,run_production]

end ThresholdHC.BlindUpper
