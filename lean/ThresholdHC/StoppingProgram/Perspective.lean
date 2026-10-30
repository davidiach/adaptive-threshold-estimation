import Mathlib

/-! Closed quadratic perspectives, including null reference states. -/

noncomputable section
open scoped ENNReal

namespace ThresholdHC.StoppingProgram

def perspective (x y : ℝ) : ℝ≥0∞ :=
  if 0 < y then ENNReal.ofReal (x^2/y) else if x = 0 then 0 else ⊤

theorem perspective_pos {x y : ℝ} (hy : 0 < y) : perspective x y = ENNReal.ofReal (x^2/y) :=
  ite_eq_left hy

theorem perspective_zero_zero : perspective 0 0 = 0 := by simp [perspective]

theorem perspective_nonzero_zero {x : ℝ} (hx : x ≠ 0) : perspective x 0 = ⊤ := by
  simp [perspective,hx]

theorem perspective_finite_iff {x y : ℝ} (_hy : 0 ≤ y) :
    perspective x y < ⊤ ↔ 0 < y ∨ x = 0 := by
  by_cases h : 0 < y
  · simp [perspective,h]
  · by_cases hx : x = 0 <;> simp [perspective,h,hx]

theorem quadratic_div_add_le {x z a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (x+z)^2/(a+b) ≤ x^2/a+z^2/b := by
  have he : x^2/a+z^2/b-(x+z)^2/(a+b) = (b*x-a*z)^2/(a*b*(a+b)) := by
    field_simp
    ring
  have h : 0 ≤ (b*x-a*z)^2/(a*b*(a+b)) := by positivity
  rw [← he] at h
  linarith

theorem perspective_add_le {x z a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    perspective (x+z) (a+b) ≤ perspective x a+perspective z b := by
  by_cases ha0 : a = 0
  · subst a
    by_cases hx : x = 0
    · subst x
      simp [perspective_zero_zero]
    · rw [perspective_nonzero_zero hx,top_add]
      exact le_top
  · have ha' := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hb0 : b = 0
    · subst b
      by_cases hz : z = 0
      · subst z
        simp [perspective_zero_zero]
      · rw [perspective_nonzero_zero hz,add_top]
        exact le_top
    · have hb' := lt_of_le_of_ne hb (Ne.symm hb0)
      rw [perspective_pos (add_pos ha' hb'), perspective_pos ha', perspective_pos hb',
        ← ENNReal.ofReal_add (div_nonneg (sq_nonneg _) ha) (div_nonneg (sq_nonneg _) hb)]
      exact ENNReal.ofReal_le_ofReal (quadratic_div_add_le ha' hb')

theorem perspective_scale (x y : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    perspective (c*x) (c*y) = ENNReal.ofReal c*perspective x y := by
  by_cases hc0 : c = 0
  · subst c
    simp [perspective_zero_zero]
  have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  by_cases hy : 0 < y
  · rw [perspective_pos (mul_pos hc' hy),perspective_pos hy,← ENNReal.ofReal_mul hc]
    congr 1
    field_simp
  · have hcy : ¬0 < c*y := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_gt hy))
    by_cases hx : x = 0
    · simp [perspective,hy,hcy,hx]
    · simp [perspective,hy,hcy,hx,mul_ne_zero hc0 hx,ENNReal.mul_top,ENNReal.ofReal_ne_zero_iff.mpr hc']

theorem perspective_cone_lower {a t z v d α : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hv : 0 < v) (hcone : z^2 ≤ a*t) :
    -(α^2*a*d^2/(4*v)) ≤ v*t-α*d*z := by
  by_cases ha0 : a = 0
  · subst a
    have hz : z = 0 := by nlinarith [sq_nonneg z]
    simp only [hz,mul_zero,zero_mul,zero_div,neg_zero,sub_zero]
    exact mul_nonneg hv.le ht
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have he : v*t-α*d*z+α^2*a*d^2/(4*v) =
        v*(t-z^2/a)+(2*v*z-α*a*d)^2/(4*a*v) := by
      field_simp
      ring
    have hzt : z^2/a ≤ t := (div_le_iff₀ ha').mpr (by simpa only [mul_comm] using hcone)
    have hn : 0 ≤ v*(t-z^2/a)+(2*v*z-α*a*d)^2/(4*a*v) := by positivity
    rw [← he] at hn
    linarith

theorem perspective_cone_attains {a v d α : ℝ} (ha : 0 < a) (hv : 0 < v) :
    let z := α*a*d/(2*v)
    let t := z^2/a
    z^2 = a*t ∧ v*t-α*d*z = -(α^2*a*d^2/(4*v)) := by
  dsimp
  constructor
  · field_simp
  · field_simp
    ring

end ThresholdHC.StoppingProgram
