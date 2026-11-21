import ThresholdHC.KnownGapRarity.Confidence

/-! The targets of `ThresholdHC.KnownGapRarity`: the flip count is the source's
`m`; the known-gap estimator is rarity-free, capped at `floor B` flips on every
path, identically `0` for `B < 2m`, and has mean squared error at most
`8 m theta/B + 4 m/B^2` for every sign law; and the computable interval covers
`theta` with probability at least `1 - delta`. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.KnownGapRarity

theorem flip_count : FlipCountStatement :=
  fun d B _ => ⟨flipCount_odd d B, flipCount_ge d B, fun m hm h => flipCount_least d B m hm h⟩

theorem known_gap_rarity_free : KnownGapRarityFreeStatement := by
  intro d _ B hB
  exact ⟨knownGap_pathwiseCap d (by linarith), knownGap_uniformBudget d (by linarith),
    fun h z => knownGapEstimator_output_of_lt h z,
    fun h q => zero_output_risk _ _ (fun z => knownGapEstimator_output_of_lt h z) q _,
    fun q => knownGap_risk_le d hB q⟩

theorem known_gap_confidence : KnownGapConfidenceStatement := by
  intro d _ B _ δ hδ0 hδ1
  exact ⟨rawEstimator_interval d B hδ0 hδ1, rawEstimator_confidence d B hδ0 hδ1,
    knownGap_confidence d B hδ0 hδ1⟩

end ThresholdHC.KnownGapRarity
