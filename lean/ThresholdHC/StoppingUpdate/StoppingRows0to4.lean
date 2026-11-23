import ThresholdHC.StoppingUpdate.StoppingPieces

/-! Kernel certificate rows for the pilot counts `j = 0, …, 4`, each evaluated
whole in the form `fastRowCheck` by its own `decide +kernel`. -/
namespace ThresholdHC.StoppingUpdate

set_option maxHeartbeats 0 in
theorem rows_0_4 (j : ℕ) (h : j < 5) : fastRowCheck j = true := by
  interval_cases j <;> decide +kernel

end ThresholdHC.StoppingUpdate
