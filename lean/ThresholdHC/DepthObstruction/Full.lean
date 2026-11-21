import ThresholdHC.DepthObstruction.Floor
import ThresholdHC.DepthObstruction.Bridge

/-! The part-1 targets of the bounded-depth obstruction, proved: the population,
cross-coin-feedback transcript identity and RMS floor of `thm:cap` in
`research/2026-10-27-nonlinear-population/upper/proof-body.tex`, for a general
per-coin cap and gap law, the formal-only cap-diameter floor, and the bridge from
the history-count cap. -/

noncomputable section
namespace ThresholdHC.DepthObstruction

/-- `thm:cap`, transcript part: matching odd moments through depth `N` and a
per-coin cap `N` give the same seed-and-transcript law, with arbitrary feedback. -/
theorem capped_transcript : CappedTranscriptStatement :=
  cappedTranscript

/-- `thm:cap`, final display: equal observable laws give RMS at least half the
target separation. -/
theorem equal_law_floor : EqualLawFloorStatement :=
  equalLawFloor

/-- Formal-only extension, not a source claim: half the cap-`N` diameter floors the
rare-prior RMS risk of every per-coin-capped population procedure. -/
theorem population_cap_floor : PopulationCapFloorStatement :=
  populationCapFloor

/-- The history-count cap of `RestrictedRMS` implies `PerCoinCap`. -/
theorem history_cap_bridge : HistoryCapBridgeStatement :=
  historyCapBridge

end ThresholdHC.DepthObstruction
