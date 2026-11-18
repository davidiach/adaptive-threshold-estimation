import ThresholdHC.UpperCost.LevelSum
import ThresholdHC.UpperWork.Moments

/-! The padded cost of one call of the distribution-blind estimator on a coin of
gap `d`: the expected cost of the levels up to `L`, plus the one flip that the
padded call takes with probability `r^{L+1}` above them, is at most
`(11/2)*min (sqrt (2^L)) d⁻¹`. -/
noncomputable section
namespace ThresholdHC.UpperCost
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem paddedWorkMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    workMomentK 1 1 L d S + rLevel ^ (L + 1) ≤ (11/2) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ := by
  unfold workMomentK
  apply padded_levelSum_le L hd hdmax
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

/-- The expected cost of the levels up to `L` of one call on a coin of gap `d`. -/
theorem cutoff_cost_mean_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (11/2) * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ - rLevel ^ (L + 1) := by
  rw [cutoff_cost_mean_eq]
  linarith [paddedWorkMoment_le L d S hd hdmax]

end ThresholdHC.UpperCost
