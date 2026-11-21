import ThresholdHC.UnknownRarity.Obstruction

/-! The obstruction to completely uniform adaptation to unknown rarity
(`docs/process/TRACK_D.md`), its fixed-budget strengthening, the expected-work
form, and the stopped-transcript absolute continuity used by the proof. -/
noncomputable section
namespace ThresholdHC.UnknownRarity

theorem unknown_rarity_obstruction : UnknownRarityObstructionStatement :=
  unknown_rarity_obstruction_proof

theorem fixed_budget_obstruction : FixedBudgetObstructionStatement :=
  fixed_budget_obstruction_proof

theorem expected_work_obstruction : ExpectedWorkObstructionStatement :=
  expected_work_obstruction_proof

theorem stopped_transcript_ac : StoppedTranscriptACStatement :=
  stopped_transcript_ac_proof

end ThresholdHC.UnknownRarity
