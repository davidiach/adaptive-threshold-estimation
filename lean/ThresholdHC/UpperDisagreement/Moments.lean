import ThresholdHC.UpperDisagreement.LevelSum
import ThresholdHC.UpperMoment.Moments
import ThresholdHC.UpperCost.Moments

/-! The second moment and the padded cost of one call on a coin of gap `d`, with
the regime term of `LevelSum`. -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem secondMomentK_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    secondMomentK 1 1 L d S ≤
      (57/5) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ + (13/50) * regimeTerm L d := by
  unfold secondMomentK
  apply disagreement_levelSum_le L hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    deltaK_secondMoment_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · exact increment_sq_negative l hd hdmax
      (by simpa [coinP, sub_eq_add_neg] using htail)
  · exact increment_sq_positive l hd hdmax
      (by simpa [coinP, sub_eq_add_neg] using htail)

theorem paddedWorkMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    workMomentK 1 1 L d S + rLevel ^ (L + 1) ≤
      (11/2) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ - (9/2) * regimeTerm L d := by
  unfold workMomentK
  apply padded_regime_le L hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    levelWork_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · have ht : HasMeanTails (tapeMeasure (coinParameter d false hd hdmax))
        (fun k ω => dyadicMean observations k ω) (1 / 2 - d) := by
      simpa [coinP, sub_eq_add_neg] using htail
    exact UpperWork.expected_work_le_survival l ht.measurable
      (fun k => UpperWork.survival_negative l k ht)
  · have ht : HasMeanTails (tapeMeasure (coinParameter d true hd hdmax))
        (fun k ω => dyadicMean observations k ω) (1 / 2 + d) := by
      simpa [coinP, sub_eq_add_neg] using htail
    exact UpperWork.expected_work_le_survival l ht.measurable
      (fun k => UpperWork.survival_positive l k ht)

end ThresholdHC.UpperDisagreement
