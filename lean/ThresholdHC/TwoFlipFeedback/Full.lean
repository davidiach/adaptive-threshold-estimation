import ThresholdHC.TwoFlipFeedback.Upper
import ThresholdHC.TwoFlipFeedback.Lower
import ThresholdHC.TwoFlipFeedback.Members

/-! The targets of `Specification.lean`. The internal constants are
`upperValue = 15442587/10^9 < 15443/10^6` and
`15475/10^6 < lowerValue = 1547585/10^8`, and
`upperValue + 32/10^6 < lowerValue`. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open scoped ENNReal

private theorem upper_lt : ENNReal.ofReal upperValue < ENNReal.ofReal (15443/1000000) :=
  (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num [upperValue])

private theorem lower_gt : ENNReal.ofReal (15475/1000000) < ENNReal.ofReal lowerValue :=
  (ENNReal.ofReal_lt_ofReal_iff (by norm_num [lowerValue])).mpr (by norm_num [lowerValue])

private theorem gap_lt : ENNReal.ofReal upperValue + ENNReal.ofReal (32/1000000) <
    ENNReal.ofReal lowerValue := by
  rw [← ENNReal.ofReal_add (by norm_num [upperValue]) (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [lowerValue])).mpr
    (by norm_num [upperValue, lowerValue])

theorem feedback_upper_bound : FeedbackUpperStatement :=
  ⟨feedbackEstimator, feedback_policy, feedback_output, feedback_cap,
    feedback_not_noninteractive, feedback_upper.trans_lt upper_lt⟩

theorem noninteractive_class : NoninteractiveClassStatement :=
  ⟨⟨sameCoinEstimator, fun _ => rfl, sameCoin_cap, sameCoin_noninteractive⟩,
    ⟨freshCoinEstimator, fun _ => rfl, freshCoin_cap, freshCoin_noninteractive⟩,
    minimax_le⟩

theorem uniform_lower_bound : UniformLowerStatement := by
  intro R _ A hcap hA
  exact uniform_lower A hcap hA

theorem noninteractive_lower : NoninteractiveLowerStatement :=
  ⟨lower_gt.trans_le minimax_lower, minimax_le⟩

theorem feedback_separation : SeparationStatement :=
  ⟨feedbackEstimator, feedback_policy, feedback_output, feedback_cap,
    feedback_not_noninteractive,
    (lt_of_le_of_lt (add_le_add feedback_upper le_rfl) gap_lt).trans_le minimax_lower⟩

end ThresholdHC.TwoFlipFeedback
