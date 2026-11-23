import ThresholdHC.StoppingUpdate.StoppingPieces

/-! Kernel certificate row for the pilot count `j = 8`, evaluated whole in
the form `fastRowCheck` by one `decide +kernel`. -/
namespace ThresholdHC.StoppingUpdate

set_option maxHeartbeats 0 in
theorem row_8 : fastRowCheck 8 = true := by decide +kernel

end ThresholdHC.StoppingUpdate
