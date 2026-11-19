import ThresholdHC.UpperCallCost.LevelSum
import ThresholdHC.UpperDisagreement.Moments

/-! The padded cost of one call on a coin of gap `d`, with the regime term of
`UpperDisagreement`: the expected cost of the levels up to `L`, plus the one
flip that the padded call takes with probability `r^{L+1}` above them, is at
most `(26/5)*min (sqrt (2^L)) d⁻¹ - (21/5)*regimeTerm L d`. -/
noncomputable section
namespace ThresholdHC.UpperCallCost
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem paddedWorkMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    workMomentK 1 1 L d S + rLevel ^ (L + 1) ≤
      (26/5) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ - (21/5) * UpperDisagreement.regimeTerm L d := by
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

theorem cutoff_cost_mean_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (26/5) * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ - (21/5) * UpperDisagreement.regimeTerm L d -
        rLevel ^ (L + 1) := by
  rw [cutoff_cost_mean_eq]
  linarith [paddedWorkMoment_le L d S hd hdmax]

end ThresholdHC.UpperCallCost
