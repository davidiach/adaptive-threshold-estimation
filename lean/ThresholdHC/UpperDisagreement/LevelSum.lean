import ThresholdHC.UpperDisagreement.Increment
import ThresholdHC.UpperMoment.LevelSum

/-! The level sums of the call second moment and of the padded call cost.

Bounding every level's disagreement by one gives `(6 + 4*sqrt 2)*sqrt (2^L)`
for the second moment. The level bounds give `(2 + sqrt 2)*321/100 + 41/100 ≤
57/5` divided by `d`. When `2^L*d^2 ≤ 1` the first is the smaller, but it exceeds
`57/5*sqrt (2^L)`. In that regime the padded call cost is at most `sqrt (2^L)`,
far below `11/2*sqrt (2^L)`. So both sums carry a regime term
`regimeTerm L d`, `sqrt (2^L)` in the regime and zero outside it: the second
moment is at most `57/5*min (sqrt (2^L)) d⁻¹ + (13/50)*regimeTerm L d`, and
the padded cost at most `11/2*min (sqrt (2^L)) d⁻¹ - (9/2)*regimeTerm L d`. Since
`(13/50)*(11/2) ≤ (57/5)*(9/2)`, the regime terms cancel in the product. -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- `sqrt (cap L)` when `cap L*d^2 ≤ 1`, and zero otherwise. -/
def regimeTerm (L : ℕ) (d : ℝ) : ℝ := if cap L * d ^ 2 ≤ 1 then Real.sqrt (cap L) else 0

theorem regimeTerm_nonneg (L : ℕ) (d : ℝ) : 0 ≤ regimeTerm L d := by
  unfold regimeTerm
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

theorem sqrt_cap_mul (L : ℕ) {d : ℝ} (hd : 0 < d) :
    Real.sqrt (cap L) * d = Real.sqrt (cap L * d ^ 2) := by
  rw [Real.sqrt_mul (cap_pos L).le, Real.sqrt_sq hd.le]

/-- The level sum of the call second moment. -/
theorem disagreement_levelSum_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (e : ℕ → ℝ) (he : ∀ l ≤ L, e l ≤ min 1 (levelBound l d)) :
    ∑ l ∈ range (L + 1), e l / pLevel l ≤
      (57 / 5) * min (Real.sqrt (cap L)) d⁻¹ + (13 / 50) * regimeTerm L d := by
  have hp : ∀ l, 0 < pLevel l := fun l => mul_pos (sub_pos.2 rLevel_lt_one) (pow_pos rLevel_pos l)
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  -- every level bounded by one
  have hone : ∑ l ∈ range (L + 1), e l / pLevel l ≤ (6 + 4 * Real.sqrt 2) * Real.sqrt (cap L) := by
    have h : ∑ l ∈ range (L + 1), e l / pLevel l ≤ ∑ l ∈ range (L + 1), (pLevel l)⁻¹ := by
      apply sum_le_sum
      intro l hl
      rw [div_eq_mul_inv]
      have h1 : e l ≤ 1 := (he l (Nat.le_of_lt_succ (mem_range.1 hl))).trans (min_le_left _ _)
      have hi : 0 ≤ (pLevel l)⁻¹ := inv_nonneg.2 (hp l).le
      nlinarith
    rw [UpperMoment.inv_pLevel_sum, ← sqrt_cap] at h
    linarith [Real.sqrt_nonneg 2]
  -- every level bounded by its level bound
  have hlev : d * ∑ l ∈ range (L + 1), e l / pLevel l ≤ 57 / 5 := by
    have h1 : ∑ l ∈ range (L + 1), e l / pLevel l ≤
        ∑ l ∈ range (L + 1), capWeight (cap l * d ^ 2) / pLevel l +
          ∑ l ∈ range (L + 1), (stopError l d + stopError (l - 1) d) / pLevel l := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro l hl
      have h2 : e l ≤ levelBound l d := (he l (Nat.le_of_lt_succ (mem_range.1 hl))).trans
        (min_le_right _ _)
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (hp l).le
      unfold levelBound at h2
      linarith
    have hcap : d * ∑ l ∈ range (L + 1), capWeight (cap l * d ^ 2) / pLevel l ≤
        (2 + Real.sqrt 2) * (321 / 100) := by
      have hterm : ∀ l ∈ range (L + 1), d * (capWeight (cap l * d ^ 2) / pLevel l) =
          (2 + Real.sqrt 2) * (Real.sqrt (cap l * d ^ 2) * capWeight (cap l * d ^ 2)) := by
        intro l _
        rw [div_eq_mul_inv, UpperMoment.inv_pLevel, UpperCost.sqrt_cap_mul_sq l hd.le]
        ring
      rw [mul_sum, sum_congr rfl hterm, ← mul_sum]
      have hd2 : d ^ 2 < 12 / 25 := by nlinarith
      exact mul_le_mul_of_nonneg_left (cap_grid_le hd hd2 (L + 1)) (by positivity)
    have hstop := stopError_levelSum_le L hd
    have := mul_le_mul_of_nonneg_left h1 hd.le
    rw [mul_add] at this
    nlinarith
  by_cases hreg : cap L * d ^ 2 ≤ 1
  · have hmin : min (Real.sqrt (cap L)) d⁻¹ = Real.sqrt (cap L) := by
      apply min_eq_left
      rw [← one_div, le_div_iff₀ hd, sqrt_cap_mul L hd]
      exact Real.sqrt_le_one.mpr hreg
    have hr : regimeTerm L d = Real.sqrt (cap L) := by unfold regimeTerm; rw [ite_eq_left hreg]
    rw [hmin, hr]
    have hs := Real.sqrt_nonneg (cap L)
    nlinarith
  · have hmin : min (Real.sqrt (cap L)) d⁻¹ = d⁻¹ := by
      apply min_eq_right
      rw [← one_div, div_le_iff₀ hd, sqrt_cap_mul L hd]
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hr : regimeTerm L d = 0 := by unfold regimeTerm; rw [ite_eq_right hreg]
    rw [hmin, hr, mul_zero, add_zero, ← div_eq_mul_inv, le_div_iff₀ hd]
    linarith

/-- The padded call cost with the regime term. -/
theorem padded_regime_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2) (w : ℕ → ℝ)
    (hw : ∀ l ≤ L, w l ≤ 1 + ∑ k ∈ range l, cap k * survivalBound l k d) :
    ∑ l ∈ range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (11 / 2) * min (Real.sqrt (cap L)) d⁻¹ - (9 / 2) * regimeTerm L d := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hp : ∀ l, 0 ≤ pLevel l := fun l => mul_nonneg (by linarith) (pow_nonneg hr0.le l)
  by_cases hreg : cap L * d ^ 2 ≤ 1
  · have hcapw : ∀ l ≤ L, w l ≤ cap l := by
      intro l hl
      refine (hw l hl).trans ?_
      have h : ∑ k ∈ range l, cap k * survivalBound l k d ≤ ∑ k ∈ range l, cap k :=
        sum_le_sum (fun k _ => mul_le_of_le_one_right (cap_pos k).le (survivalBound_le_one l k d))
      have hg : ∑ k ∈ range l, cap k = cap l - 1 := by
        change ∑ k ∈ range l, (2 : ℝ) ^ k = (2 : ℝ) ^ l - 1
        rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) l]
        norm_num
      linarith
    have h := sum_le_sum (fun l (hl : l ∈ range (L + 1)) => mul_le_mul_of_nonneg_left
      (hcapw l (Nat.le_of_lt_succ (mem_range.1 hl))) (hp l))
    rw [levelWeight_cap_sum, ← sqrt_cap] at h
    have hrL : rLevel ^ (L + 1) ≤ rLevel := by
      calc
        rLevel ^ (L + 1) ≤ rLevel ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
        _ = rLevel := pow_one _
    have hmin : min (Real.sqrt (cap L)) d⁻¹ = Real.sqrt (cap L) := by
      apply min_eq_left
      rw [← one_div, le_div_iff₀ hd, sqrt_cap_mul L hd]
      exact Real.sqrt_le_one.mpr hreg
    have hreg' : regimeTerm L d = Real.sqrt (cap L) := by unfold regimeTerm; rw [ite_eq_left hreg]
    rw [hmin, hreg']
    linarith
  · have hreg' : regimeTerm L d = 0 := by unfold regimeTerm; rw [ite_eq_right hreg]
    rw [hreg', mul_zero, sub_zero]
    exact UpperCost.padded_levelSum_le L hd hdmax w hw

end ThresholdHC.UpperDisagreement
