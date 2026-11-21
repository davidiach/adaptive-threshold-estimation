import ThresholdHC.StoppingUpdate.StoppingPieces

/-! Kernel certificate pieces for the pilot counts `j = 0, …, 4`. The single tactic block
below checks the 27 pieces of each row one after another, each with its
own `decide +kernel` kernel check. -/
namespace ThresholdHC.StoppingUpdate

set_option maxHeartbeats 0 in
theorem pieces_0_4 (j : ℕ) (h : j < 5) (a b c : Fin 3) :
    pieceCheck j a b c = true := by
  interval_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

end ThresholdHC.StoppingUpdate
