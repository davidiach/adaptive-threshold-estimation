import ThresholdHC.ClippingBoundary.Specification

/-! Pointwise polynomial inequalities behind the bounded-kurtosis transfer.

The note's proof uses Hölder's inequality with exponents `3/2` and `3` and a
Paley–Zygmund step. The formal proof integrates the pointwise inequalities
below instead, so it needs neither real powers nor indicator events:

* `quartic_young`: `3s²x² ≤ 2s³|x| + x⁴` for `s ≥ 0`, from
  `y⁴ - 3s²y² + 2s³y = y(y-s)²(y+2s)` with `y = |x|`;
* `clip_lower_pos` and `clip_lower_neg`: the clipped error dominates the
  truncated error toward the farther endpoint of `[0,ρ]`;
* `truncation_lower`: `4cty - t²y² ≤ 4c·min(y,c)` for `y ≥ 0`, `c > 0`,
  `t ≤ 1`;
* `tangent_lower`: `2az - a² ≤ z²`. -/
noncomputable section
namespace ThresholdHC.ClippingBoundary
open ThresholdHC.HardBudget

theorem quartic_young (s x : ℝ) (hs : 0 ≤ s) : 3 * s ^ 2 * x ^ 2 ≤ 2 * s ^ 3 * |x| + x ^ 4 := by
  have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h4 : x ^ 4 = |x| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h2, h4]
  have hy := abs_nonneg x
  have hprod : 0 ≤ |x| * (|x| - s) ^ 2 * (|x| + 2 * s) :=
    mul_nonneg (mul_nonneg hy (sq_nonneg _)) (by linarith)
  nlinarith [hprod]

theorem clip_lower_pos (ρ θ x : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ ρ / 2) :
    min (max (x - θ) 0) (ρ / 2) ^ 2 ≤ (clipEstimate ρ x - θ) ^ 2 := by
  rcases le_or_gt x θ with hx | hx
  · have h1 : max (x - θ) 0 = 0 := max_eq_right (by linarith)
    have h2 : min (0 : ℝ) (ρ / 2) = 0 := min_eq_left (by linarith)
    rw [h1, h2, zero_pow two_ne_zero]
    exact sq_nonneg _
  · have hw0 : 0 ≤ min (max (x - θ) 0) (ρ / 2) := le_min (le_max_right _ _) (by linarith)
    have hmax : max (x - θ) 0 = x - θ := max_eq_left (by linarith)
    have hw : min (max (x - θ) 0) (ρ / 2) ≤ clipEstimate ρ x - θ := by
      rw [hmax]
      have hc : min ρ x ≤ clipEstimate ρ x := le_max_right _ _
      rcases le_total ρ x with hρx | hρx
      · rw [min_eq_left hρx] at hc
        have := min_le_right (x - θ) (ρ / 2)
        linarith
      · rw [min_eq_right hρx] at hc
        have := min_le_left (x - θ) (ρ / 2)
        linarith
    exact pow_le_pow_left₀ hw0 hw 2

theorem clip_lower_neg (ρ θ x : ℝ) (hθ : ρ / 2 ≤ θ) (hθρ : θ ≤ ρ) :
    min (max (θ - x) 0) (ρ / 2) ^ 2 ≤ (clipEstimate ρ x - θ) ^ 2 := by
  rcases le_or_gt θ x with hx | hx
  · have hρ : 0 ≤ ρ := by linarith
    have h1 : max (θ - x) 0 = 0 := max_eq_right (by linarith)
    have h2 : min (0 : ℝ) (ρ / 2) = 0 := min_eq_left (by linarith)
    rw [h1, h2, zero_pow two_ne_zero]
    exact sq_nonneg _
  · have hρ : 0 ≤ ρ := by linarith
    have hw0 : 0 ≤ min (max (θ - x) 0) (ρ / 2) := le_min (le_max_right _ _) (by linarith)
    have hmax : max (θ - x) 0 = θ - x := max_eq_left (by linarith)
    have hclip : clipEstimate ρ x = max 0 x := by
      unfold clipEstimate
      rw [min_eq_right (by linarith)]
    have hw : min (max (θ - x) 0) (ρ / 2) ≤ θ - clipEstimate ρ x := by
      rw [hmax, hclip]
      rcases le_total 0 x with h0 | h0
      · rw [max_eq_right h0]
        have := min_le_left (θ - x) (ρ / 2)
        linarith
      · rw [max_eq_left h0]
        have := min_le_right (θ - x) (ρ / 2)
        linarith
    have hsq : (clipEstimate ρ x - θ) ^ 2 = (θ - clipEstimate ρ x) ^ 2 := by ring
    rw [hsq]
    exact pow_le_pow_left₀ hw0 hw 2

theorem truncation_lower (y c t : ℝ) (hy : 0 ≤ y) (hc : 0 < c) (ht1 : t ≤ 1) :
    4 * c * t * y - t ^ 2 * y ^ 2 ≤ 4 * c * min y c := by
  rcases le_total y c with hyc | hyc
  · rw [min_eq_left hyc]
    have h1 : t * y ≤ y := by nlinarith
    nlinarith [sq_nonneg (t * y)]
  · rw [min_eq_right hyc]
    nlinarith [sq_nonneg (t * y - 2 * c)]

theorem tangent_lower (a z : ℝ) : 2 * a * z - a ^ 2 ≤ z ^ 2 := by
  nlinarith [sq_nonneg (z - a)]

/-- The positive and negative parts add to the absolute value. -/
theorem max_add_max_neg (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]
    ring

/-- The positive and negative parts differ by the value. -/
theorem max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

end ThresholdHC.ClippingBoundary
