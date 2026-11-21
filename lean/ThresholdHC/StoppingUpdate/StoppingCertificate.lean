import ThresholdHC.StoppingUpdate.StoppingRows0to4
import ThresholdHC.StoppingUpdate.StoppingRow5
import ThresholdHC.StoppingUpdate.StoppingRow6
import ThresholdHC.StoppingUpdate.StoppingRow7
import ThresholdHC.StoppingUpdate.StoppingRow8
import ThresholdHC.StoppingUpdate.StoppingRow9
import ThresholdHC.StoppingUpdate.StoppingRow10
import ThresholdHC.StoppingUpdate.StoppingRow11
import ThresholdHC.StoppingUpdate.StoppingRow12
import ThresholdHC.StoppingUpdate.StoppingRow13
import ThresholdHC.StoppingUpdate.StoppingRows14to18

/-! The two certificate facts of the research module
`research/2026-11-18-stopping-update/StoppingCertificate.lean`, with the same
statements. There each `rowCheck j` was one kernel evaluation; here each row is
assembled by `row_of_pieces` from its 27 pieces, checked in the row modules.
`total` is copied verbatim. -/
namespace ThresholdHC.StoppingUpdate

theorem certified (j : Fin 19) : rowCheck j = true := by
  apply row_of_pieces
  fin_cases j
  · exact pieces_0_4 0 (by decide)
  · exact pieces_0_4 1 (by decide)
  · exact pieces_0_4 2 (by decide)
  · exact pieces_0_4 3 (by decide)
  · exact pieces_0_4 4 (by decide)
  · exact pieces_5
  · exact pieces_6
  · exact pieces_7
  · exact pieces_8
  · exact pieces_9
  · exact pieces_10
  · exact pieces_11
  · exact pieces_12
  · exact pieces_13
  · exact pieces_14_18 14 (by decide) (by decide)
  · exact pieces_14_18 15 (by decide) (by decide)
  · exact pieces_14_18 16 (by decide) (by decide)
  · exact pieces_14_18 17 (by decide) (by decide)
  · exact pieces_14_18 18 (by decide) (by decide)

set_option maxHeartbeats 0 in
theorem total : 186844275^2 * 10^6 ≤ pilotSum 18 0 := by decide +kernel

end ThresholdHC.StoppingUpdate
