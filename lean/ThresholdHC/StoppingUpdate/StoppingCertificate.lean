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
checked in the form `fastRowCheck` in the row modules, and `rowCheck_eq_fast`
turns it into `rowCheck j`. `total` is copied verbatim. -/
namespace ThresholdHC.StoppingUpdate

theorem certified (j : Fin 19) : rowCheck j = true := by
  rw [rowCheck_eq_fast]
  fin_cases j
  · exact rows_0_4 0 (by decide)
  · exact rows_0_4 1 (by decide)
  · exact rows_0_4 2 (by decide)
  · exact rows_0_4 3 (by decide)
  · exact rows_0_4 4 (by decide)
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact rows_14_18 14 (by decide) (by decide)
  · exact rows_14_18 15 (by decide) (by decide)
  · exact rows_14_18 16 (by decide) (by decide)
  · exact rows_14_18 17 (by decide) (by decide)
  · exact rows_14_18 18 (by decide) (by decide)

set_option maxHeartbeats 0 in
theorem total : 186844275^2 * 10^6 ≤ pilotSum 18 0 := by decide +kernel

end ThresholdHC.StoppingUpdate
