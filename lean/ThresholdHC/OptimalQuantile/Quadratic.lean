import ThresholdHC.OptimalQuantile.Tangents

noncomputable section
open Real
namespace ThresholdHC.OptimalQuantile

/-- Exact elimination of the common nonnegative scale in a square-root price. -/
theorem scaled_root_bound_iff {g a d : ℝ} (hg : 0 ≤ g) (ha : 0 < a) (hd : 0 ≤ d) :
    (∀ t : ℝ, 0 ≤ t → sqrt (t*g) ≤ d+a*t) ↔ g ≤ 4*a*d := by
  constructor
  · intro h
    have ht : 0 ≤ g/(4*a^2) := div_nonneg hg (by positivity)
    have hb := h (g/(4*a^2)) ht
    have he : (g/(4*a^2))*g = (g/(2*a))^2 := by
      field_simp [ne_of_gt ha]
      ring
    rw [he,sqrt_sq (div_nonneg hg (by positivity))] at hb
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*a by positivity)
    have hl : (4*a)*(g/(2*a)) = 2*g := by
      field_simp [ne_of_gt ha]
      ring
    have hr : (4*a)*(d+a*(g/(4*a^2))) = 4*a*d+g := by
      field_simp [ne_of_gt ha]
    rw [hl,hr] at hm
    linarith
  · intro h t ht
    apply sqrt_le_iff.mpr
    refine ⟨add_nonneg hd (mul_nonneg ha.le ht),?_⟩
    have hb := mul_le_mul_of_nonneg_left h ht
    nlinarith only [hb,sq_nonneg (d-a*t)]

end ThresholdHC.OptimalQuantile
