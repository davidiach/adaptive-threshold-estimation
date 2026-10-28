import ThresholdHC.BlindUpper.CallPlan

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open scoped ENNReal
def phaseLabels (phase n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => Nat.pair phase i.val)

theorem phaseLabels_succ (phase n : ℕ) :
    phaseLabels phase (n+1) = phaseLabels phase n ++ [Nat.pair phase n] := by
  unfold phaseLabels
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

theorem callWords_phaseLabels (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (phase n : ℕ) :
    callWords L r s (phaseLabels phase n) = phaseWord L r s phase n := by
  simp [callWords,phaseLabels,phaseWord,phaseWords,List.flatMap,List.map_ofFn]
  rfl

theorem phasePlan_of_actions (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool)
    (c : BatchControl) (phase n : ℕ)
    (ha : ∀ i < n, controlLabel (batchRun L r (c,[]) (phaseWord L r s phase i)).1 =
      some (Nat.pair phase i)) :
    CallPlan L r s c (phaseLabels phase n) (batchRun L r (c,[]) (phaseWord L r s phase n)).1 := by
  induction n with
  | zero => simp only [phaseLabels,phaseWord,phaseWords,List.ofFn_zero,List.flatten_nil,batchRun,List.foldl_nil]; exact .nil c
  | succ n ih =>
    have hp := ih (fun i hi => ha i (by omega))
    let mid := (batchRun L r (c,[]) (phaseWord L r s phase n)).1
    let next := controlAdvance L r mid (batchCallWord L r s (Nat.pair phase n))
    have hs : CallPlan L r s mid [Nat.pair phase n] next := .cons (ha n (by omega)) (.nil _)
    have ht : CallPlan L r s c (phaseLabels phase (n+1)) next := by
      rw [phaseLabels_succ]
      exact hp.append hs
    have he := congrArg Prod.fst ht.state_eq
    rw [callWords_phaseLabels] at he
    rw [he]
    exact ht

theorem firstPilot_plan (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) :
    CallPlan L r s (.pilotOne 0) (phaseLabels 0 (a+1)) (.pilotTwo a 0) := by
  have h := phasePlan_of_actions L r s (.pilotOne 0) 0 (a+1) (by
    intro i hi
    change controlLabel (batchRun L r batchInitial (phaseWord L r s 0 i)).1 = _
    rw [run_first_pilot_prefix L r s i (fun k hk => ((firstSuccess_eq _ _).mp ha).2 k (by omega))]
    rfl)
  change CallPlan L r s (.pilotOne 0) (phaseLabels 0 (a+1))
    (batchRun L r batchInitial (phaseWord L r s 0 (a+1))).1 at h
  rw [run_first_pilot L r s a ha] at h
  exact h

theorem secondPilot_plan (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (hb : firstSuccess (phaseMark L r s 1) = b) :
    CallPlan L r s (.pilotTwo a 0) (phaseLabels 1 (b+1)) (.production (a+b) []) := by
  have h := phasePlan_of_actions L r s (.pilotTwo a 0) 1 (b+1) (by
    intro i hi
    rw [run_second_pilot_prefix L r s a i (fun k hk => ((firstSuccess_eq _ _).mp hb).2 k (by omega))]
    rfl)
  rw [run_second_pilot L r s a b hb] at h
  exact h

theorem production_plan (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (f : ℕ) :
    CallPlan L r s (.production f []) (phaseLabels 2 (f+1)) (.stopped (phaseWords L r s 2 (f+1))) := by
  have h := phasePlan_of_actions L r s (.production f []) 2 (f+1) (by
    intro i hi
    rw [run_production_prefix L r s f i (by omega)]
    simp [controlLabel])
  rw [run_production L r s f] at h
  exact h

def fullBatchLabels (a b : ℕ) : List ℕ :=
  phaseLabels 0 (a+1) ++ phaseLabels 1 (b+1) ++ phaseLabels 2 (a+b+1)

theorem fullBatch_plan (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (a b : ℕ)
    (ha : firstSuccess (phaseMark L r s 0) = a) (hb : firstSuccess (phaseMark L r s 1) = b) :
    CallPlan L r s (.pilotOne 0) (fullBatchLabels a b) (.stopped (phaseWords L r s 2 (a+b+1))) :=
  ((firstPilot_plan L r s a ha).append (secondPilot_plan L r s a b hb)).append
    (production_plan L r s (a+b))

end ThresholdHC.BlindUpper
