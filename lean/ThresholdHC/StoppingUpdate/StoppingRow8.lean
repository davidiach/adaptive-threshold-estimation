import ThresholdHC.StoppingUpdate.StoppingPieces

/-! Kernel certificate pieces for the pilot count `j = 8`. The single tactic block
below checks the 27 pieces of each row one after another, each with its
own `decide +kernel` kernel check. -/
namespace ThresholdHC.StoppingUpdate

set_option maxHeartbeats 0 in
theorem pieces_8 (a b c : Fin 3) : pieceCheck 8 a b c = true := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

end ThresholdHC.StoppingUpdate
