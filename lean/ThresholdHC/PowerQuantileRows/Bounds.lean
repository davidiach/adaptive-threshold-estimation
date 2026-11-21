import ThresholdHC.CriticalWindow.Remark

/-! Elementary bounds on the pieces of the uniform rate (W7) for a fixed
exponent: the power tail `T_α(x, ρ)`, the core cost `Φ_α(ρ)` and the entropy
factor `1 + log N_α(ρ)`. With `P = ρ^{1-1/α}` and `s = ρ^{1/α}`:

* for `α ≠ 1`, `T = (α x P - x^α)/(α - 1)` (`tail_formula`);
* for `α < 1` and `x < s`, `x^α ≤ T ≤ x^α/(1 - α)` and `P x ≤ x^α`;
* at `α = 1` and `x < ρ`, `T = x (1 + log(ρ/x))`;
* for `α > 1`, `T ≤ α/(α - 1) · P x`, and `P x ≤ T` when `x < s`;
* `ρ Φ ≤ α/(2 - α) · P^2` for `α < 2`, and
  `α(1 - (1/4)^{1-2/α})/(α - 2) ≤ Φ ≤ α/(α - 2)` for `α > 2`;
* for `α ≠ 2`, `1 + log N ≤ 1 + log(max 1 (1/|α - 2|))`;
* at `α = 2`, `x √(ρ L H)/2 ≤ x √(ρ Φ K) ≤ x √(ρ L H)` with `L H` the critical log
  factor. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.PowerQuantileRows
open ThresholdHC.PowerWindow ThresholdHC.CriticalWindow

theorem entropy_factor_ge_one {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    1 ≤ 1 + Real.log (effectiveScales α ρ) := by
  linarith [Real.log_nonneg (effective_scales_ge_one hα hρ hρ1)]

theorem entropy_factor_le {α ρ : ℝ} (hα : 0 < α) (hα2 : α ≠ 2) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    1 + Real.log (effectiveScales α ρ) ≤ 1 + Real.log (max 1 (1 / |α - 2|)) := by
  have hN := effective_scales_ge_one hα hρ hρ1
  have hle : effectiveScales α ρ ≤ max 1 (1 / |α - 2|) := by
    unfold effectiveScales
    rw [ite_eq_right hα2]
    exact min_le_right _ _
  linarith [Real.log_le_log (by linarith) hle]

theorem entropy_cap_ge_one (α : ℝ) : 1 ≤ 1 + Real.log (max 1 (1 / |α - 2|)) := by
  linarith [Real.log_nonneg (le_max_left (1 : ℝ) (1 / |α - 2|))]

/-- The closed form of the power tail away from exponent one. -/
theorem tail_formula {α x ρ : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hρ : 0 < ρ) (hx : 0 < x) :
    powerTail α x ρ = (α * x * ρ ^ (1 - 1/α) - x ^ α) / (α - 1) := by
  have hs := quantile_scale_pos (α := α) hρ
  have hα1' : α - 1 ≠ 0 := sub_ne_zero.2 hα1
  unfold powerTail
  rw [integral_rpow (Or.inr ⟨fun h => hα1 (by linarith), notMem_uIcc_of_lt hx hs⟩),
    show α - 2 + 1 = α - 1 by ring, scale_rpow hρ,
    show (α - 1) / α = 1 - 1/α by field_simp, Real.rpow_sub_one hx.ne']
  field_simp
  ring

theorem rpow_cross {α x ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) :
    ρ ^ (1 - 1/α) * x = powerQuantileScale α ρ ^ (α - 1) * x := by
  rw [scale_rpow hρ, show (α - 1) / α = 1 - 1/α by field_simp]

theorem rpow_self_eq {α x : ℝ} (hx : 0 < x) : x ^ α = x ^ (α - 1) * x := by
  rw [Real.rpow_sub_one hx.ne']
  field_simp

/-- Below exponent one, `x ρ^{1-1/α} ≤ x^α` once `x ≤ ρ^{1/α}`. -/
theorem cross_le_of_le_one {α x ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hx : 0 < x)
    (hxs : x ≤ powerQuantileScale α ρ) : ρ ^ (1 - 1/α) * x ≤ x ^ α := by
  rw [rpow_cross hα hρ, rpow_self_eq hx]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hx hxs (by linarith)) hx.le

/-- Above exponent one, `x^α ≤ x ρ^{1-1/α}` once `x ≤ ρ^{1/α}`. -/
theorem cross_ge_of_one_le {α x ρ : ℝ} (hα1 : 1 ≤ α) (hρ : 0 < ρ) (hx : 0 < x)
    (hxs : x ≤ powerQuantileScale α ρ) : x ^ α ≤ ρ ^ (1 - 1/α) * x := by
  have hα : 0 < α := by linarith
  rw [rpow_cross hα hρ, rpow_self_eq hx]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hx.le hxs (by linarith)) hx.le

theorem tail_upper_lt_one {α x ρ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hx : 0 < x) :
    powerTail α x ρ ≤ 1 / (1 - α) * x ^ α := by
  rw [tail_formula hα hα1.ne hρ hx]
  have hP : 0 ≤ ρ ^ (1 - 1/α) := Real.rpow_nonneg hρ.le _
  have h1 : 0 < 1 - α := by linarith
  rw [show (α * x * ρ ^ (1 - 1/α) - x ^ α) / (α - 1) =
      (x ^ α - α * x * ρ ^ (1 - 1/α)) / (1 - α) by
    rw [← neg_div_neg_eq]; ring_nf]
  have he : 1 / (1 - α) * x ^ α * (1 - α) = x ^ α := by field_simp
  rw [div_le_iff₀ h1, he]
  nlinarith [mul_nonneg (mul_nonneg hα.le hx.le) hP]

theorem tail_lower_lt_one {α x ρ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hx : 0 < x)
    (hxs : x < powerQuantileScale α ρ) : x ^ α ≤ powerTail α x ρ := by
  rw [tail_formula hα hα1.ne hρ hx]
  have h1 : α - 1 < 0 := by linarith
  have hc := cross_le_of_le_one hα hα1.le hρ hx hxs.le
  rw [le_div_iff_of_neg h1]
  nlinarith [mul_le_mul_of_nonneg_left hc hα.le]

theorem tail_upper_gt_one {α x ρ : ℝ} (hα1 : 1 < α) (hρ : 0 < ρ) (hx : 0 < x) :
    powerTail α x ρ ≤ α / (α - 1) * (ρ ^ (1 - 1/α) * x) := by
  have hα : 0 < α := by linarith
  rw [tail_formula hα hα1.ne' hρ hx]
  have h1 : 0 < α - 1 := by linarith
  have hxa : 0 ≤ x ^ α := Real.rpow_nonneg hx.le _
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right h1]
  nlinarith

theorem tail_lower_gt_one {α x ρ : ℝ} (hα1 : 1 < α) (hρ : 0 < ρ) (hx : 0 < x)
    (hxs : x < powerQuantileScale α ρ) : ρ ^ (1 - 1/α) * x ≤ powerTail α x ρ := by
  have hα : 0 < α := by linarith
  rw [tail_formula hα hα1.ne' hρ hx]
  have h1 : 0 < α - 1 := by linarith
  have hc := cross_ge_of_one_le hα1.le hρ hx hxs.le
  rw [le_div_iff₀ h1]
  nlinarith

theorem scale_one {ρ : ℝ} : powerQuantileScale 1 ρ = ρ := by
  unfold powerQuantileScale
  norm_num

/-- The power tail at exponent one below the quantile scale. -/
theorem tail_one {x ρ : ℝ} (hρ : 0 < ρ) (hx : 0 < x) :
    powerTail 1 x ρ = x * (1 + Real.log (ρ / x)) := by
  unfold powerTail
  rw [scale_one, show (1 : ℝ) - 2 = -1 by norm_num]
  simp only [Real.rpow_neg_one, Real.rpow_one]
  rw [integral_inv_of_pos hx hρ]
  ring

theorem phi_upper_lt_two {α ρ : ℝ} (hα : 0 < α) (hα2 : α < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ρ * powerPhi α ρ ≤ α / (2 - α) * (ρ ^ (1 - 1/α)) ^ 2 := by
  have hphi := power_phi_closed α ρ hα hρ hρ1
  rw [ite_eq_right hα2.ne] at hphi
  rw [hphi, rpow_sq_two_sub hρ]
  have hp : ρ * ρ ^ (1 - 2/α) = ρ ^ (2 - 2/α) := by
    rw [show (2 : ℝ) - 2/α = 1 + (1 - 2/α) by ring, Real.rpow_add hρ, Real.rpow_one]
  have h2 : 0 < 2 - α := by linarith
  rw [← hp, show α * (1 - ρ ^ (1 - 2/α)) / (α - 2) = α * (ρ ^ (1 - 2/α) - 1) / (2 - α) by
    rw [← neg_div_neg_eq]; ring_nf]
  rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff_of_pos_right h2]
  nlinarith [mul_pos hα hρ]

theorem phi_upper_gt_two {α ρ : ℝ} (hα2 : 2 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    powerPhi α ρ ≤ α / (α - 2) := by
  have hα : 0 < α := by linarith
  have hphi := power_phi_closed α ρ hα hρ hρ1
  rw [ite_eq_right hα2.ne'] at hphi
  rw [hphi]
  have h2 : 0 < α - 2 := by linarith
  have hp : 0 ≤ ρ ^ (1 - 2/α) := Real.rpow_nonneg hρ.le _
  rw [div_le_div_iff_of_pos_right h2]
  nlinarith

theorem phi_const_pos {α : ℝ} (hα2 : 2 < α) :
    0 < α * (1 - (1/4 : ℝ) ^ (1 - 2/α)) / (α - 2) := by
  have hα : 0 < α := by linarith
  have he : 0 < 1 - 2/α := by
    have : 2/α < 1 := by rw [div_lt_one hα]; exact hα2
    linarith
  have hq : (1/4 : ℝ) ^ (1 - 2/α) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) he
  have h2 : 0 < α - 2 := by linarith
  apply div_pos _ h2
  apply mul_pos hα
  linarith

theorem phi_lower_gt_two {α ρ : ℝ} (hα2 : 2 < α) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    α * (1 - (1/4 : ℝ) ^ (1 - 2/α)) / (α - 2) ≤ powerPhi α ρ := by
  have hα : 0 < α := by linarith
  have hphi := power_phi_closed α ρ hα hρ (by linarith)
  rw [ite_eq_right hα2.ne'] at hphi
  rw [hphi]
  have he : 0 ≤ 1 - 2/α := by
    have : 2/α ≤ 1 := by rw [div_le_one hα]; exact hα2.le
    linarith
  have hq : ρ ^ (1 - 2/α) ≤ (1/4 : ℝ) ^ (1 - 2/α) := Real.rpow_le_rpow hρ.le hρ4 he
  have h2 : 0 < α - 2 := by linarith
  rw [div_le_div_iff_of_pos_right h2]
  nlinarith

/-- Below exponent two, the core term is at most a constant multiple of `ρ^{1-1/α} x`. -/
theorem root_upper_lt_two {α ρ x : ℝ} (hα : 0 < α) (hα2 : α < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hx : 0 < x) :
    x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤
      Real.sqrt (α * (1 + Real.log (max 1 (1 / |α - 2|))) / (2 - α)) *
        (ρ ^ (1 - 1/α) * x) := by
  set K := 1 + Real.log (effectiveScales α ρ) with hK
  set Kc := 1 + Real.log (max 1 (1 / |α - 2|)) with hKc
  set P := ρ ^ (1 - 1/α) with hP
  have hK1 : 1 ≤ K := entropy_factor_ge_one hα hρ hρ1
  have hKle : K ≤ Kc := entropy_factor_le hα hα2.ne hρ hρ1
  have hphi := phi_upper_lt_two hα hα2 hρ hρ1
  have hphi0 : 0 ≤ ρ * powerPhi α ρ := mul_nonneg hρ.le (power_phi_pos hα hρ hρ1).le
  have h2 : 0 < 2 - α := by linarith
  have hc0 : 0 ≤ α / (2 - α) * P ^ 2 := by positivity
  have hmain : ρ * powerPhi α ρ * K ≤ α * Kc / (2 - α) * P ^ 2 := by
    calc ρ * powerPhi α ρ * K ≤ α / (2 - α) * P ^ 2 * Kc :=
          mul_le_mul hphi hKle (by linarith) hc0
      _ = α * Kc / (2 - α) * P ^ 2 := by ring
  have hP0 : 0 ≤ P := Real.rpow_nonneg hρ.le _
  have hs := Real.sqrt_le_sqrt hmain
  rw [Real.sqrt_mul' (α * Kc / (2 - α)) (sq_nonneg P), Real.sqrt_sq hP0] at hs
  calc x * Real.sqrt (ρ * powerPhi α ρ * K) ≤ x * (Real.sqrt (α * Kc / (2 - α)) * P) :=
        mul_le_mul_of_nonneg_left hs hx.le
    _ = _ := by ring

/-- Above exponent two, the core term is at most a constant multiple of `√ρ x`. -/
theorem root_upper_gt_two {α ρ x : ℝ} (hα2 : 2 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hx : 0 < x) :
    x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤
      Real.sqrt (α * (1 + Real.log (max 1 (1 / |α - 2|))) / (α - 2)) *
        (Real.sqrt ρ * x) := by
  have hα : 0 < α := by linarith
  set K := 1 + Real.log (effectiveScales α ρ) with hK
  set Kc := 1 + Real.log (max 1 (1 / |α - 2|)) with hKc
  have hK1 : 1 ≤ K := entropy_factor_ge_one hα hρ hρ1
  have hKle : K ≤ Kc := entropy_factor_le hα hα2.ne' hρ hρ1
  have hphi := phi_upper_gt_two hα2 hρ hρ1
  have hphi0 : 0 ≤ powerPhi α ρ := (power_phi_pos hα hρ hρ1).le
  have h2 : 0 < α - 2 := by linarith
  have hmain : ρ * powerPhi α ρ * K ≤ α * Kc / (α - 2) * ρ := by
    have h1 : powerPhi α ρ * K ≤ α / (α - 2) * Kc :=
      mul_le_mul hphi hKle (by linarith) (by positivity)
    calc ρ * powerPhi α ρ * K = ρ * (powerPhi α ρ * K) := by ring
      _ ≤ ρ * (α / (α - 2) * Kc) := mul_le_mul_of_nonneg_left h1 hρ.le
      _ = α * Kc / (α - 2) * ρ := by ring
  have hs := Real.sqrt_le_sqrt hmain
  have hc0 : (0 : ℝ) ≤ α * Kc / (α - 2) := by have := entropy_cap_ge_one α; positivity
  rw [Real.sqrt_mul hc0 ρ] at hs
  calc x * Real.sqrt (ρ * powerPhi α ρ * K) ≤
        x * (Real.sqrt (α * Kc / (α - 2)) * Real.sqrt ρ) :=
        mul_le_mul_of_nonneg_left hs hx.le
    _ = _ := by ring

/-- Above exponent two, the core term is at least a constant multiple of `√ρ x`. -/
theorem root_lower_gt_two {α ρ x : ℝ} (hα2 : 2 < α) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : 0 < x) :
    Real.sqrt (α * (1 - (1/4 : ℝ) ^ (1 - 2/α)) / (α - 2)) * (Real.sqrt ρ * x) ≤
      x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) := by
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  set φ := α * (1 - (1/4 : ℝ) ^ (1 - 2/α)) / (α - 2) with hφ
  have hφ0 : 0 < φ := phi_const_pos hα2
  have hK1 := entropy_factor_ge_one hα hρ hρ1
  have hphi := phi_lower_gt_two hα2 hρ hρ4
  have hmain : φ * ρ ≤ ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ)) := by
    have h1 : φ ≤ powerPhi α ρ * (1 + Real.log (effectiveScales α ρ)) := by
      nlinarith
    nlinarith
  have hs := Real.sqrt_le_sqrt hmain
  rw [Real.sqrt_mul hφ0.le] at hs
  calc Real.sqrt φ * (Real.sqrt ρ * x) = x * (Real.sqrt φ * Real.sqrt ρ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hx.le

/-- At exponent two the core term is `x √(ρ L H)` within the factor two. -/
theorem quadratic_root_bounds {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : 0 < x) :
    1/2 * (x * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ)) ≤
      x * Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ∧
    x * Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ≤
      x * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ) := by
  obtain ⟨hΦl, hΦu, hNL, hLN⟩ := quadratic_scales_bounds hρ hρ4
  have hℓ1 := log_inv_ge_one hρ hρ4
  set L := 1 + Real.log (1/ρ) with hL
  set H := 1 + Real.log L with hH
  set N := effectiveScales 2 ρ with hN
  have hN1 : 1 ≤ N := effective_scales_ge_one (by norm_num) hρ (by linarith)
  have hL1 : 1 ≤ L := by linarith
  have hH1 : 1 ≤ H := by linarith [Real.log_nonneg hL1]
  have hcrit : ThresholdHC.CriticalEntropy.criticalLogFactor ρ = L * H := by
    unfold ThresholdHC.CriticalEntropy.criticalLogFactor; rfl
  have hKu : 1 + Real.log N ≤ H := by
    linarith [Real.log_le_log (by linarith) hNL]
  have hKl : H / 2 ≤ 1 + Real.log N := by
    have h := Real.log_le_log (by linarith) hLN
    rw [Real.log_pow] at h
    push_cast at h
    have := Real.log_nonneg hN1
    linarith
  have hK0 : 0 ≤ 1 + Real.log N := by linarith
  have hΦ0 : 0 ≤ powerPhi 2 ρ := by linarith
  rw [hcrit]
  constructor
  · have hmain : (1/2 : ℝ)^2 * (ρ * (L * H)) ≤ ρ * powerPhi 2 ρ * (1 + Real.log N) := by
      have h1 : (L / 2) * (H / 2) ≤ powerPhi 2 ρ * (1 + Real.log N) :=
        mul_le_mul hΦl hKl (by linarith) hΦ0
      nlinarith
    have hs := Real.sqrt_le_sqrt hmain
    rw [← mul_sqrt_eq (by norm_num : (0 : ℝ) ≤ 1/2)] at hs
    calc 1/2 * (x * Real.sqrt (ρ * (L * H))) = x * (1/2 * Real.sqrt (ρ * (L * H))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hx.le
  · have hmain : ρ * powerPhi 2 ρ * (1 + Real.log N) ≤ ρ * (L * H) := by
      have h1 : powerPhi 2 ρ * (1 + Real.log N) ≤ L * H :=
        mul_le_mul hΦu hKu hK0 (by linarith)
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmain) hx.le

theorem critical_factor_ge_one {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    1 ≤ ThresholdHC.CriticalEntropy.criticalLogFactor ρ := by
  have hℓ1 := log_inv_ge_one hρ hρ4
  unfold ThresholdHC.CriticalEntropy.criticalLogFactor
  have hL1 : 1 ≤ 1 + Real.log (1/ρ) := by linarith
  have hH1 : 1 ≤ 1 + Real.log (1 + Real.log (1/ρ)) := by linarith [Real.log_nonneg hL1]
  nlinarith

/-- Two clipped quantities are comparable when the unclipped ones are, with
factors `c ≤ 1 ≤ C`. -/
theorem clip_bounds {ρ Z V c C : ℝ} (hρ : 0 ≤ ρ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hC1 : 1 ≤ C)
    (hl : c * Z ≤ V) (hu : V ≤ C * Z) :
    c * min ρ Z ≤ min ρ V ∧ min ρ V ≤ C * min ρ Z := by
  constructor
  · rw [mul_min_of_nonneg _ _ hc0]
    exact min_le_min (by nlinarith) hl
  · rw [mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ C)]
    exact min_le_min (by nlinarith) hu

end ThresholdHC.PowerQuantileRows
