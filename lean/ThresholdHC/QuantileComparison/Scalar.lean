import ThresholdHC.QuantileComparison.Specification
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Proof of Lemma 3. Write `c = a²`, `T = b²` and `r = √(T² + v²)`, so that
`√(Tc) = ab` and `r² = b⁴ + v²`. The squared inequality is `0 ≤ H` with
`H = ((8/5)(r + a²) - b²)² - (v² + 2a²b² + 2vab)`, and
`r·H = (3ar - 2bv)²/6 + (64/25)·r·(a² + (181r - 260b²)/256)²
  + (1104·r·(b² - (217/276)r)² + (12320/69)·r³ + 2048·b²·(b² - (3/4)r)²)/3072
  + ((2b² + 3r)/3)·(r² - b⁴ - v²)`.
This is the note's normalized proof multiplied by `r³`, with `s = b²/r`: the
Young step, the completed square in `z²`, and the cubic `p(s)` written as
`1104(w - 5/138)² + 12320/69 + 2048w²s` with `w = s - 3/4`. -/
namespace ThresholdHC.QuantileComparison

/-- The squared form of Lemma 3, multiplied by `r`, as a sum of nonnegative terms. -/
theorem scalar_certificate (a b v r : ℝ) (hr : 0 ≤ r) (hr2 : r ^ 2 = (b ^ 2) ^ 2 + v ^ 2) :
    0 ≤ r * ((8 / 5 * (r + a ^ 2) - b ^ 2) ^ 2 -
      (v ^ 2 + 2 * b ^ 2 * a ^ 2 + 2 * v * (a * b))) := by
  have identity : r * ((8 / 5 * (r + a ^ 2) - b ^ 2) ^ 2 -
      (v ^ 2 + 2 * b ^ 2 * a ^ 2 + 2 * v * (a * b))) =
      (3 * a * r - 2 * b * v) ^ 2 / 6
        + 64 / 25 * (r * (a ^ 2 + (181 * r - 260 * b ^ 2) / 256) ^ 2)
        + (1104 * (r * (b ^ 2 - 217 / 276 * r) ^ 2) + 12320 / 69 * r ^ 3
          + 2048 * (b ^ 2 * (b ^ 2 - 3 / 4 * r) ^ 2)) / 3072 := by
    linear_combination (2 * b ^ 2 + 3 * r) / 3 * hr2
  rw [identity]
  have h1 := sq_nonneg (3 * a * r - 2 * b * v)
  have h2 := mul_nonneg hr (sq_nonneg (a ^ 2 + (181 * r - 260 * b ^ 2) / 256))
  have h3 := mul_nonneg hr (sq_nonneg (b ^ 2 - 217 / 276 * r))
  have h4 := pow_nonneg hr 3
  have h5 := mul_nonneg (sq_nonneg b) (sq_nonneg (b ^ 2 - 3 / 4 * r))
  linarith

/-- Lemma 3: `T + √(v² + 2Tc + 2v√(Tc)) ≤ (8/5)(√(T² + v²) + c)` for `T, v, c ≥ 0`. -/
theorem scalar_comparison : ScalarComparisonStatement := by
  intro T v c hT hv hc
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ c = a ^ 2 :=
    ⟨Real.sqrt c, Real.sqrt_nonneg c, (Real.sq_sqrt hc).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 ≤ b ∧ T = b ^ 2 :=
    ⟨Real.sqrt T, Real.sqrt_nonneg T, (Real.sq_sqrt hT).symm⟩
  have hw : Real.sqrt (b ^ 2 * a ^ 2) = a * b := by
    rw [show b ^ 2 * a ^ 2 = (a * b) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg ha hb)
  rw [hw]
  have hr : 0 ≤ Real.sqrt ((b ^ 2) ^ 2 + v ^ 2) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt ((b ^ 2) ^ 2 + v ^ 2) ^ 2 = (b ^ 2) ^ 2 + v ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hbr : b ^ 2 ≤ Real.sqrt ((b ^ 2) ^ 2 + v ^ 2) :=
    calc b ^ 2 = Real.sqrt ((b ^ 2) ^ 2) := (Real.sqrt_sq (sq_nonneg b)).symm
      _ ≤ Real.sqrt ((b ^ 2) ^ 2 + v ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg v))
  generalize Real.sqrt ((b ^ 2) ^ 2 + v ^ 2) = r at hr hr2 hbr ⊢
  have hD : 0 ≤ 8 / 5 * (r + a ^ 2) - b ^ 2 := by nlinarith [sq_nonneg a]
  have hsq : v ^ 2 + 2 * b ^ 2 * a ^ 2 + 2 * v * (a * b) ≤
      (8 / 5 * (r + a ^ 2) - b ^ 2) ^ 2 := by
    rcases hr.lt_or_eq with hpos | hzero
    · exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (scalar_certificate a b v r hr hr2) hpos)
    · subst hzero
      have hv0 : v = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg (b ^ 2)])
      have hb2 : b ^ 2 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg v])
      subst hv0
      rw [hb2]
      nlinarith [sq_nonneg (8 / 5 * (0 + a ^ 2) - 0)]
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hD] at hs
  linarith

end ThresholdHC.QuantileComparison
