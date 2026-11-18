import ThresholdHC.UpperMoment.LevelSum
import ThresholdHC.UpperConstant.Moments

/-! The second moment of one call of the distribution-blind estimator with the
sharper disagreement bound: at most `72/5` times `min (sqrt (2^L)) d⁻¹`, in
place of `23`. -/
noncomputable section
namespace ThresholdHC.UpperMoment
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem secondMomentK_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    secondMomentK 1 1 L d S ≤ (72/5) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ := by
  unfold secondMomentK
  apply secondMoment_levelSum_le L d hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    deltaK_secondMoment_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · exact increment_secondMoment_negative l hd hdmax
      (by simpa [coinP, sub_eq_add_neg] using htail)
  · exact increment_secondMoment_positive l hd hdmax
      (by simpa [coinP, sub_eq_add_neg] using htail)

/-- The second moment of one call on a coin of gap `d`. -/
theorem cutoff_secondMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (72/5) * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ := by
  rw [cutoff_secondMoment_eq]
  exact secondMomentK_le L d S hd hdmax

end ThresholdHC.UpperMoment
