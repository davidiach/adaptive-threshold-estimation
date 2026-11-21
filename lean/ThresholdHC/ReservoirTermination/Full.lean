import ThresholdHC.ReservoirTermination.Examples

/-!
The countable-reservoir termination counterexample (research note
`research/2026-10-27-minimax-audit/formal/stopping_bridge.tex`, the proposition on
one-law finite work and the interior-gap remark), stated against the specification.
-/

noncomputable section
namespace ThresholdHC.ReservoirTermination

theorem walk_first_passage : WalkFirstPassageStatement := walk_first_passage_holds

theorem half_gap_counterexample : HalfGapExampleStatement := half_gap_example

theorem quarter_gap_counterexample : QuarterGapExampleStatement := quarter_gap_example

theorem naive_bridge_fails : NaiveBridgeFailsStatement := naive_bridge_fails_proof

theorem reservoir_counterexample : ReservoirCounterexampleStatement :=
  reservoir_counterexample_proof

theorem original_experiment : OriginalExperimentStatement := original_experiment_proof

end ThresholdHC.ReservoirTermination
