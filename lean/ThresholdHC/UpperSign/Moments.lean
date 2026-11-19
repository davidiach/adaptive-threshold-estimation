import ThresholdHC.UpperSign.LevelSum
import ThresholdHC.UpperDisagreement.Moments

/-! The second moment of one call on a coin of gap `d` with the sign-change
bound. -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

section SignMoments
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem secondMomentK_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    secondMomentK 1 1 L d S ≤
      (89/10) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ + (69/25) * UpperDisagreement.regimeTerm L d := by
  unfold secondMomentK
  apply sign_levelSum_le L hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    deltaK_secondMoment_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · have ht : HasMeanTails (tapeMeasure (coinParameter d false hd hdmax))
        (fun k ω => dyadicMean observations k ω) (1 / 2 - d) := by
      simpa [coinP, sub_eq_add_neg] using htail
    exact sign_increment_le l _ hd hdmax 0 (fun L => Tier2.Model.error_negative_union L hd ht)
      (fun L => early_negative L hd ht)
  · have ht : HasMeanTails (tapeMeasure (coinParameter d true hd hdmax))
        (fun k ω => dyadicMean observations k ω) (1 / 2 + d) := by
      simpa [coinP, sub_eq_add_neg] using htail
    exact sign_increment_le l _ hd hdmax 1 (fun L => Tier2.Model.error_positive_union L hd ht)
      (fun L => early_positive L hd ht)

end SignMoments

end ThresholdHC.UpperSign
