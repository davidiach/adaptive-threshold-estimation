import ThresholdHC.BiasAudit.Counterexample
import ThresholdHC.BiasAudit.SmallerThreshold

/-! The bias-audit targets of `proposals/constants/BIAS_AUDIT.md`, proved. -/
noncomputable section
namespace ThresholdHC.BiasAudit

/-- BIAS_AUDIT.md:49-69: the grid winner `(1/4,1/2)` has error at least `(2/5)^128` at
`d = 1/10`, `N = 2^97`, more than `2907` times the v4 envelope. -/
theorem grid_winner_counterexample : GridWinnerCounterexampleStatement :=
  gridWinnerCounterexample

/-- The grid winner `(1/4,1/2)` fails the v4 Lemma 6 envelope. -/
theorem grid_winner_fails_envelope : GridWinnerFailsEnvelopeStatement :=
  gridWinnerFailsEnvelope

/-- BIAS_AUDIT.md:6-41: for `k1 ≥ 0`, `k2 ≥ 1` the classifier keeps the v4 envelope. -/
theorem smaller_threshold_error : SmallerThresholdErrorStatement :=
  smallerThresholdError

end ThresholdHC.BiasAudit
