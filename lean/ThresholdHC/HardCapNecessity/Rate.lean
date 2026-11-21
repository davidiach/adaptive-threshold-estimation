import ThresholdHC.HardCapNecessity.Specification

/-! The explicit rate `K(b) = min(1/4, 2 sqrt((1/4)/b))`: its value at `1/2`,
its square-root scaling, its square, and the eventual drop of `32 C^2 K(B)^2`
below the floor `1/512`. -/

noncomputable section
namespace ThresholdHC.HardCapNecessity

theorem rate_nonneg (b : ℝ) : 0 ≤ rareRate b :=
  le_min (by norm_num) (by positivity)

/-- `K(b) = 1/4` for every positive `b ≤ 16`. -/
theorem rate_small {b : ℝ} (hb : 0 < b) (hb' : b ≤ 16) : rareRate b = 1/4 := by
  apply min_eq_left
  have h : (1/8 : ℝ) ≤ Real.sqrt ((1/4) / b) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hb]
    nlinarith
  linarith

theorem rate_half : rareRate (1/2) = 1/4 := rate_small (by norm_num) (by norm_num)

theorem rate_scale {b b' : ℝ} (hb : 1/2 ≤ b) (hbb : b ≤ b') :
    rareRate b ≤ Real.sqrt (b'/b) * rareRate b' := by
  have hb0 : 0 < b := by linarith
  have hb0' : 0 < b' := by linarith
  have hs : 1 ≤ Real.sqrt (b'/b) := Real.one_le_sqrt.mpr ((one_le_div hb0).mpr hbb)
  have he : (1/4 : ℝ) / b = (b'/b) * ((1/4) / b') := by field_simp
  have hroot : 2 * Real.sqrt ((1/4) / b) = Real.sqrt (b'/b) * (2 * Real.sqrt ((1/4) / b')) := by
    rw [he, Real.sqrt_mul (by positivity)]; ring
  unfold rareRate
  rw [mul_min_of_nonneg _ _ (by positivity), hroot]
  exact min_le_min (by linarith) le_rfl

theorem rate_sq_le_inv {b : ℝ} (hb : 0 < b) : (rareRate b)^2 ≤ 1/b := by
  have h1 : rareRate b ≤ 2 * Real.sqrt ((1/4) / b) := min_le_right _ _
  have h2 : (2 * Real.sqrt ((1/4) / b))^2 = 1/b := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  calc (rareRate b)^2 ≤ (2 * Real.sqrt ((1/4) / b))^2 :=
        pow_le_pow_left₀ (rate_nonneg b) h1 2
    _ = 1/b := h2

theorem min_le_rate_sq {b : ℝ} (hb : 0 < b) : min (1/16) (1/b) ≤ (rareRate b)^2 := by
  unfold rareRate
  rcases min_cases (1/4 : ℝ) (2 * Real.sqrt ((1/4) / b)) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; norm_num
  · rw [h, mul_pow, Real.sq_sqrt (by positivity)]
    calc min (1/16) (1/b) ≤ 1/b := min_le_right _ _
      _ = 2^2 * ((1/4) / b) := by ring

/-- `32 C^2 K(B)^2 < 1/512` for all large `B`. -/
theorem rate_eventually_below (C : ℝ) :
    ∃ B₀ : ℝ, 4 ≤ B₀ ∧ ∀ B : ℝ, B₀ ≤ B → 32 * C^2 * (rareRate B)^2 < 1/512 := by
  refine ⟨max 4 (16384 * C^2 + 1), le_max_left _ _, ?_⟩
  intro B hB
  have h4 : 4 ≤ B := (le_max_left _ _).trans hB
  have hC : 16384 * C^2 + 1 ≤ B := (le_max_right _ _).trans hB
  have hB0 : 0 < B := by linarith
  calc 32 * C^2 * (rareRate B)^2 ≤ 32 * C^2 * (1/B) :=
        mul_le_mul_of_nonneg_left (rate_sq_le_inv hB0) (by positivity)
    _ < 1/512 := by
        rw [mul_one_div, div_lt_iff₀ hB0]
        nlinarith

theorem rare_rate_holds : RareRateStatement :=
  ⟨rate_half, fun b _ => rate_nonneg b, fun _ _ hb hbb => rate_scale hb hbb,
    rate_eventually_below⟩

end ThresholdHC.HardCapNecessity
