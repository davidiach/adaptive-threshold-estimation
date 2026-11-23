import ThresholdHC.StoppingUpdate.StoppingPieces

/-! Kernel certificate rows for the pilot counts `j = 14, …, 18`, each
evaluated whole in the form `fastRowCheck` by its own `decide +kernel`. -/
namespace ThresholdHC.StoppingUpdate

set_option maxHeartbeats 0 in
theorem rows_14_18 (j : ℕ) (hl : 14 ≤ j) (h : j < 19) : fastRowCheck j = true := by
  interval_cases j <;> decide +kernel

end ThresholdHC.StoppingUpdate
