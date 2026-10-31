import ThresholdHC.StoppingProgram.Perspective

/-! The closed quadratic perspective is lower semicontinuous, including
singular zero-reference states. -/

noncomputable section
open Set
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.StoppingProgram

theorem perspective_le_finite_iff (x y : ℝ) (hy : 0 ≤ y) (z : ℝ≥0∞) (hz : z ≠ ⊤) :
    perspective x y ≤ z ↔ x^2 ≤ z.toReal*y := by
  by_cases hy0 : y = 0
  · subst y
    by_cases hx : x = 0
    · simp [hx,perspective]
    · have hs : 0 < x^2 := sq_pos_of_ne_zero hx
      simp [perspective,hx,hz,not_le.mpr hs]
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [perspective_pos hy',ENNReal.ofReal_le_iff_le_toReal hz,div_le_iff₀ hy']

theorem lowerSemicontinuous_perspective {X : Type*} [TopologicalSpace X]
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ x, 0 ≤ g x) :
    LowerSemicontinuous (fun x => perspective (f x) (g x)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro z
  by_cases hz : z = ⊤
  · simp [hz]
  · have he : (fun x => perspective (f x) (g x)) ⁻¹' Iic z =
        {x | (f x)^2 ≤ z.toReal*g x} := by
      ext x
      exact perspective_le_finite_iff (f x) (g x) (hgn x) z hz
    rw [he]
    exact isClosed_le (hf.pow 2) (continuous_const.mul hg)

end ThresholdHC.Genie
