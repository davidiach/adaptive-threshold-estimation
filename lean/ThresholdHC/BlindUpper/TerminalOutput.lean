import ThresholdHC.BlindUpper.BatchMachine

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier2
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
theorem processHistory_add (x : ProcessTape) (n m : ℕ) :
    processHistory x (n+m) = processHistory x n ++ processHistory (fun i => x (n+i)) m := by
  unfold processHistory processPrefix
  rw [List.ofFn_add,List.filterMap_append]
  rfl

theorem firstSuccess_finite_le (ω : ℕ → Bool) (n : ℕ) (hn : ω n = true) :
    ∃ k ≤ n, firstSuccess ω = k := by
  classical
  have h : ∃ k, ω k = true := ⟨n,hn⟩
  exact ⟨Nat.find h,Nat.find_min' h hn,by simp [firstSuccess,h]⟩

theorem batchRun_absorbs (L : ℕ) (r : BatchSeed) (s : BatchMachineState)
    (hs : controlLabel s.1 = none) (xs : List Bool) : batchRun L r s xs = s := by
  rcases s with ⟨c,ws⟩
  cases c with
  | pilotOne i => simp [controlLabel] at hs
  | pilotTwo a i => simp [controlLabel] at hs
  | production f samples => simp [controlLabel] at hs
  | stopped samples => exact batchRun_stopped L r samples ws xs

/-- Any observed halt determines the terminal output, regardless of the tail. -/
theorem batchOutput_at_halt (L : ℕ) (r : BatchSeed) (x : ProcessTape) (n : ℕ)
    (hn : batchPolicy L r (processHistory x n) = none) :
    batchOutput L (r,x) = controlOutput L r (batchRun L r batchInitial (processHistory x n)).1 := by
  have hmark : (batchPolicy L r (processHistory x n)).isNone = true := by rw [hn]; rfl
  obtain ⟨k,hkn,hk⟩ := firstSuccess_finite_le
    (fun j => (batchPolicy L r (processHistory x j)).isNone) n hmark
  have hkstop : batchPolicy L r (processHistory x k) = none :=
    Option.isNone_iff_eq_none.mp ((firstSuccess_eq _ _).mp hk).1
  have he : batchRun L r batchInitial (processHistory x n) =
      batchRun L r batchInitial (processHistory x k) := by
    conv_lhs => rw [show n = k+(n-k) by omega,processHistory_add,batchRun_append]
    exact batchRun_absorbs L r _ hkstop _
  change controlOutput L r (batchRun L r batchInitial (processHistory x (batchHaltTime L (r,x)).toNat)).1 = _
  rw [show batchHaltTime L (r,x) = k from hk]
  simp only [ENat.toNat_natCast]
  rw [he]

end ThresholdHC.BlindUpper
