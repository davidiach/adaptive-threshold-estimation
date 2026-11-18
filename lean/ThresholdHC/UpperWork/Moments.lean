import ThresholdHC.UpperWork.LevelSum
import ThresholdHC.UpperConstant.Moments

/-! The expected cost of one call of the distribution-blind estimator with the
sharper per-level work bound: at most `248/25` times
`min (sqrt (2^L)) d⁻¹`, in place of `527/7`. -/
noncomputable section
namespace ThresholdHC.UpperWork
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem workMomentK_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    workMomentK 1 1 L d S ≤ (248/25) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ := by
  unfold workMomentK
  apply work_levelSum_le L d hd hdmax
  · intro l hl
    rw [← coinParameter_val d S hd hdmax,
      levelWork_eq_integral L l hl (coinParameter d S hd hdmax)]
    exact Model.expected_work_le_cap (tape_mean_tails (coinParameter d S hd hdmax)).measurable l
  · intro l hl hx
    rw [← coinParameter_val d S hd hdmax,
      levelWork_eq_integral L l hl (coinParameter d S hd hdmax)]
    have htail := tape_mean_tails (coinParameter d S hd hdmax)
    cases S
    · exact expected_work_negative l hd hdmax
        (by simpa [coinP, sub_eq_add_neg] using htail) hx
    · exact expected_work_positive l hd hdmax
        (by simpa [coinP, sub_eq_add_neg] using htail) hx

/-- The expected cost of one call on a coin of gap `d`. -/
theorem cutoff_cost_mean_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (248/25) * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ := by
  rw [cutoff_cost_mean_eq]
  exact workMomentK_le L d S hd hdmax

end ThresholdHC.UpperWork
