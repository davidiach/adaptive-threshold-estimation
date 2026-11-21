import ThresholdHC.TwoFlipDominance.AlmostSureLower
import ThresholdHC.TwoFlipDominance.Members

/-! The targets of `Specification.lean`. The internal constants are those of
`ThresholdHC.TwoFlipFeedback`: `upperValue = 15442587/10^9`,
`15475/10^6 < lowerValue = 1547585/10^8` and
`upperValue + 32/10^6 < lowerValue`. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance
open MeasureTheory
open scoped ENNReal
open ThresholdHC.TwoFlipFeedback

private theorem lower_gt' : ENNReal.ofReal (15475/1000000) < ENNReal.ofReal lowerValue :=
  (ENNReal.ofReal_lt_ofReal_iff (by norm_num [lowerValue])).mpr (by norm_num [lowerValue])

private theorem gap_lt' : ENNReal.ofReal upperValue + ENNReal.ofReal (32/1000000) <
    ENNReal.ofReal lowerValue := by
  rw [← ENNReal.ofReal_add (by norm_num [upperValue]) (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [lowerValue])).mpr
    (by norm_num [upperValue, lowerValue])

theorem dominance_pathwise : PathwiseDominanceStatement := by
  intro R _ A hcap hA
  exact pathwise_dominance A hcap hA

theorem dominance_seed : SeedDominanceStatement := by
  intro R _ A hcap hA
  exact seed_dominance A hcap hA

theorem local_class : LocalClassStatement :=
  ⟨fun A hcap => pathwise_almostSure A hcap,
    ⟨sameCoinEstimator, fun _ => rfl, sameCoin_cap, sameCoin_local⟩,
    ⟨freshCoinEstimator, fun _ => rfl, freshCoin_cap, freshCoin_local⟩,
    local_minimax_le⟩

theorem local_uniform_lower_bound : LocalUniformLowerStatement := by
  intro R _ A hcap hA
  exact uniform_lower_ae A hcap hA

theorem local_lower : LocalLowerStatement :=
  ⟨lower_gt'.trans_le local_minimax_lower, local_minimax_le⟩

theorem local_separation : LocalSeparationStatement :=
  ⟨feedbackEstimator, feedback_policy, feedback_output, feedback_cap,
    pathwise_almostSure feedbackEstimator feedback_cap, feedback_not_local,
    (lt_of_le_of_lt (add_le_add feedback_upper le_rfl) gap_lt').trans_le local_minimax_lower⟩

end ThresholdHC.TwoFlipDominance
