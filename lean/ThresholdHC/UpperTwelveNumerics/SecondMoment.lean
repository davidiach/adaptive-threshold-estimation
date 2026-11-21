import ThresholdHC.UpperTwelveNumerics.Specification
import ThresholdHC.UpperQuarter.Moments

/-! The one-call second moment: `d*E[Y_L^2 | d,S] ≤ (2+sqrt 2)*89/50 + 41/100 < 6.49`.

`UpperQuarter.quarter_levelSum_le` combines the vote-change weights, at most
`(2+sqrt 2)*89/50` after multiplication by `d` (`UpperQuarter.quarter_grid_le`),
with the wrong-side early stops, at most `41/100`
(`UpperDisagreement.stopError_levelSum_le`), and then rounds the sum up to
`13/2`. Here the sum is kept (`quarter_levelSum_d_le`), and the second moment
follows as in `UpperQuarter.secondMomentK_le` (`secondMoment_d_le`). -/
noncomputable section
namespace ThresholdHC.UpperTwelveNumerics
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

section LevelSum
open Real Uniform713

/-- The level sum of the call second moment, multiplied by `d`. -/
theorem quarter_levelSum_d_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (e : ℕ → ℝ) (he : ∀ l ≤ L, e l ≤ min 1 (UpperQuarter.quarterWeight l d +
      UpperDisagreement.stopError l d + UpperDisagreement.stopError (l - 1) d)) :
    d * ∑ l ∈ range (L + 1), e l / pLevel l ≤ (2 + Real.sqrt 2) * (89 / 50) + 41 / 100 := by
  have hp : ∀ l, 0 < pLevel l := fun l => mul_pos (sub_pos.2 rLevel_lt_one) (pow_pos rLevel_pos l)
  have h1 : ∑ l ∈ range (L + 1), e l / pLevel l ≤
      ∑ l ∈ range (L + 1), UpperQuarter.quarterWeight l d / pLevel l +
        ∑ l ∈ range (L + 1), (UpperDisagreement.stopError l d +
          UpperDisagreement.stopError (l - 1) d) / pLevel l := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro l hl
    have h2 := (he l (Nat.le_of_lt_succ (mem_range.1 hl))).trans (min_le_right _ _)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (hp l).le
    linarith
  have hw : d * ∑ l ∈ range (L + 1), UpperQuarter.quarterWeight l d / pLevel l ≤
      (2 + Real.sqrt 2) * (89 / 50) := by
    have hterm : ∀ l ∈ range (L + 1), d * (UpperQuarter.quarterWeight l d / pLevel l) =
        (2 + Real.sqrt 2) * (Real.sqrt (cap l * d ^ 2) * UpperQuarter.quarterWeight l d) := by
      intro l _
      rw [div_eq_mul_inv, UpperMoment.inv_pLevel, UpperCost.sqrt_cap_mul_sq l hd.le]
      ring
    rw [mul_sum, sum_congr rfl hterm, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (UpperQuarter.quarter_grid_le hd hdmax (L + 1)) (by positivity)
  have hstop := UpperDisagreement.stopError_levelSum_le L hd
  have := mul_le_mul_of_nonneg_left h1 hd.le
  rw [mul_add] at this
  linarith

theorem secondMoment_expr_lt : (2 + Real.sqrt 2) * (89 / 50) + 41 / 100 < (649 / 100 : ℝ) := by
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  nlinarith

end LevelSum

section Moments
open MeasureTheory Finset ThresholdHC ThresholdHC.Uniform713 ThresholdHC.Tier2
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

/-- `d*E[Y_L^2 | d,S] ≤ (2+sqrt 2)*89/50 + 41/100` for every `0 < d ≤ 1/2`. -/
theorem secondMoment_d_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    d * secondMomentK 1 1 L d S ≤ (2 + Real.sqrt 2) * (89 / 50) + 41 / 100 := by
  unfold secondMomentK
  apply quarter_levelSum_d_le L hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    deltaK_secondMoment_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · have ht : HasMeanTails (tapeMeasure (coinParameter d false hd hdmax))
        (fun k ω => dyadicMean observations k ω) (1 / 2 - d) := by
      simpa [coinP, sub_eq_add_neg] using htail
    exact UpperQuarter.quarter_increment_le l _ hd hdmax 0
      (fun L => Tier2.Model.error_negative_union L hd ht)
      (fun L => UpperSign.early_negative L hd ht)
  · have ht : HasMeanTails (tapeMeasure (coinParameter d true hd hdmax))
        (fun k ω => dyadicMean observations k ω) (1 / 2 + d) := by
      simpa [coinP, sub_eq_add_neg] using htail
    exact UpperQuarter.quarter_increment_le l _ hd hdmax 1
      (fun L => Tier2.Model.error_positive_union L hd ht)
      (fun L => UpperSign.early_positive L hd ht)

end Moments

end ThresholdHC.UpperTwelveNumerics
