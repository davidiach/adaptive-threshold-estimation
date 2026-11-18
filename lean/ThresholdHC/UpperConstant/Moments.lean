import ThresholdHC.BlindUpper.CutoffBiasWork
import ThresholdHC.Proofs.Tier2.ClassifierProb

/-! The level sums behind the call moments of the distribution-blind
estimator, without weakening their constants. The existing proofs show the
second-moment sum below 23 and the work sum below (17/7)*31 = 527/7, and then
weaken them to the frozen targets 85 and 149. -/
noncomputable section
namespace ThresholdHC.UpperConstant
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem secondMoment_levelSum_le (L : ℕ) (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1 / 2)
    (e : ℕ → ℝ) (he : ∀ l ≤ L, e l ≤ min 1 (3 / (cap l * d ^ 2) ^ 2)) :
    (∑ l ∈ range (L + 1), e l / pLevel l) ≤ 23 * min (Real.sqrt (cap L)) d⁻¹ := by
  have hle : (∑ l ∈ range (L + 1), e l / pLevel l) ≤
      ∑ l ∈ range (L + 1), secondMomentEnvelope l d := by
    apply sum_le_sum
    intro l hl
    have hlL : l ≤ L := Nat.le_of_lt_succ (mem_range.mp hl)
    exact div_le_div_of_nonneg_right (he l hlL) (levelProb_pos l).le
  exact hle.trans (by simpa only [one_div] using (sum_secondMomentEnvelope_lt L d hd hdhalf).le)

theorem workMoment_levelSum_le (L : ℕ) (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1 / 2)
    (w : ℕ → ℝ) (hw : ∀ l ≤ L, w l ≤ 17 * workEnvelope l d) :
    (∑ l ∈ range (L + 1), pLevel l * w l) ≤ (527/7) * min (Real.sqrt (cap L)) d⁻¹ := by
  have hle : (∑ l ∈ range (L + 1), pLevel l * w l) ≤
      (17 / 7 : ℝ) * ∑ l ∈ range (L + 1), levelProb l * (7 * workEnvelope l d) := by
    rw [mul_sum]
    apply sum_le_sum
    intro l hl
    have hlL : l ≤ L := Nat.le_of_lt_succ (mem_range.mp hl)
    have h := mul_le_mul_of_nonneg_left (hw l hlL) (levelProb_pos l).le
    convert h using 1 <;> simp only [pLevel, levelProb]
    ring
  have hs := mul_le_mul_of_nonneg_left (sum_weightedWorkEnvelope_lt L d hd hdhalf).le
    (by norm_num : (0 : ℝ) ≤ 17 / 7)
  have hconst : (17 / 7 : ℝ) * (31 * min (Real.sqrt (cap L)) (1/d)) =
      (527/7) * min (Real.sqrt (cap L)) d⁻¹ := by
    rw [one_div]; ring
  exact (hle.trans hs).trans hconst.le

theorem secondMomentK_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    secondMomentK 1 1 L d S ≤ 23 * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ := by
  unfold secondMomentK
  apply secondMoment_levelSum_le L d hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    deltaK_secondMoment_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · exact Model.increment_secondMoment_negative l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)
  · exact Model.increment_secondMoment_positive l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)

theorem workMomentK_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    workMomentK 1 1 L d S ≤ (527/7) * min (Real.sqrt ((2 : ℝ) ^ L)) d⁻¹ := by
  unfold workMomentK
  apply workMoment_levelSum_le L d hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    levelWork_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · exact Model.expected_work_negative_bound l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)
  · exact Model.expected_work_positive_bound l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)

/-- The second moment of one call on a coin of gap `d`. -/
theorem cutoff_secondMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      23 * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ := by
  rw [cutoff_secondMoment_eq]
  exact secondMomentK_le L d S hd hdmax

/-- The expected cost of one call on a coin of gap `d`. -/
theorem cutoff_cost_mean_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      (527/7) * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ := by
  rw [cutoff_cost_mean_eq]
  exact workMomentK_le L d S hd hdmax

end ThresholdHC.UpperConstant
