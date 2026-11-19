import ThresholdHC.UpperSign.Increment
import ThresholdHC.UpperDisagreement.LevelSum

/-! The level sum of the call second moment with the sign-change bound.

Bounding every level by one gives `(6 + 4*sqrt 2)*sqrt (2^L)`. The weights give
`(2 + sqrt 2)*247/100 + 41/100 ≤ 89/10` divided by `d`. As in
`UpperDisagreement`, the two combine into
`89/10*min (sqrt (2^L)) d⁻¹ + (69/25)*regimeTerm L d`. -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

section SignLevelSum
open Real Uniform713

/-- The level sum of the call second moment with the sign-change bound. -/
theorem sign_levelSum_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (e : ℕ → ℝ) (he : ∀ l ≤ L, e l ≤ min 1 (signWeight l d + UpperDisagreement.stopError l d +
      UpperDisagreement.stopError (l - 1) d)) :
    ∑ l ∈ range (L + 1), e l / pLevel l ≤
      (89 / 10) * min (Real.sqrt (cap L)) d⁻¹ + (69 / 25) * UpperDisagreement.regimeTerm L d := by
  have hp : ∀ l, 0 < pLevel l := fun l => mul_pos (sub_pos.2 rLevel_lt_one) (pow_pos rLevel_pos l)
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hone : ∑ l ∈ range (L + 1), e l / pLevel l ≤ (6 + 4 * Real.sqrt 2) * Real.sqrt (cap L) := by
    have h : ∑ l ∈ range (L + 1), e l / pLevel l ≤ ∑ l ∈ range (L + 1), (pLevel l)⁻¹ := by
      apply sum_le_sum
      intro l hl
      rw [div_eq_mul_inv]
      have h1 : e l ≤ 1 := (he l (Nat.le_of_lt_succ (mem_range.1 hl))).trans (min_le_left _ _)
      have hi : 0 ≤ (pLevel l)⁻¹ := inv_nonneg.2 (hp l).le
      nlinarith
    rw [UpperMoment.inv_pLevel_sum, ← UpperWork.sqrt_cap] at h
    linarith [Real.sqrt_nonneg 2]
  have hlev : d * ∑ l ∈ range (L + 1), e l / pLevel l ≤ 89 / 10 := by
    have h1 : ∑ l ∈ range (L + 1), e l / pLevel l ≤
        ∑ l ∈ range (L + 1), signWeight l d / pLevel l +
          ∑ l ∈ range (L + 1), (UpperDisagreement.stopError l d +
            UpperDisagreement.stopError (l - 1) d) / pLevel l := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro l hl
      have h2 := (he l (Nat.le_of_lt_succ (mem_range.1 hl))).trans (min_le_right _ _)
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (hp l).le
      linarith
    have hw : d * ∑ l ∈ range (L + 1), signWeight l d / pLevel l ≤
        (2 + Real.sqrt 2) * (247 / 100) := by
      have hterm : ∀ l ∈ range (L + 1), d * (signWeight l d / pLevel l) =
          (2 + Real.sqrt 2) * (Real.sqrt (cap l * d ^ 2) * signWeight l d) := by
        intro l _
        rw [div_eq_mul_inv, UpperMoment.inv_pLevel, UpperCost.sqrt_cap_mul_sq l hd.le]
        ring
      rw [mul_sum, sum_congr rfl hterm, ← mul_sum]
      exact mul_le_mul_of_nonneg_left (sign_grid_le hd hdmax (L + 1)) (by positivity)
    have hstop := UpperDisagreement.stopError_levelSum_le L hd
    have := mul_le_mul_of_nonneg_left h1 hd.le
    rw [mul_add] at this
    nlinarith
  by_cases hreg : cap L * d ^ 2 ≤ 1
  · have hmin : min (Real.sqrt (cap L)) d⁻¹ = Real.sqrt (cap L) := by
      apply min_eq_left
      rw [← one_div, le_div_iff₀ hd, UpperDisagreement.sqrt_cap_mul L hd]
      exact Real.sqrt_le_one.mpr hreg
    have hr : UpperDisagreement.regimeTerm L d = Real.sqrt (cap L) := by
      unfold UpperDisagreement.regimeTerm; rw [ite_eq_left hreg]
    rw [hmin, hr]
    have hs := Real.sqrt_nonneg (cap L)
    nlinarith
  · have hmin : min (Real.sqrt (cap L)) d⁻¹ = d⁻¹ := by
      apply min_eq_right
      rw [← one_div, div_le_iff₀ hd, UpperDisagreement.sqrt_cap_mul L hd]
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hr : UpperDisagreement.regimeTerm L d = 0 := by
      unfold UpperDisagreement.regimeTerm; rw [ite_eq_right hreg]
    rw [hmin, hr, mul_zero, add_zero, ← div_eq_mul_inv, le_div_iff₀ hd]
    linarith

end SignLevelSum

end ThresholdHC.UpperSign
