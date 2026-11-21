import ThresholdHC.PowerQuantileRows.Specification
import ThresholdHC.PowerQuantileRows.Bounds

/-! Reading the uniform rate (W7) as the table row, one exponent regime at a
time. Write `s = ρ^{1/α}`, `T` for the power tail and `Y` for the core term, so
that the rate is `min{ρ, T + Y}` for `x < s` and `ρ` otherwise. Each regime
shows that `ρ` is at most the row's inner term `Z` once `x ≥ s`, and that
`c Z ≤ T + Y ≤ C Z` for `x < s`, with `c ≤ 1 ≤ C` depending only on `α`.

| regime | `Z` | `c` | `C` |
|---|---|---|---|
| `0 < α < 1` | `x^α` | `1` | `1/(1-α) + k_α` |
| `α = 1` | `x(1 + log₊(ρ/x))` | `1` | `1 + k_1` |
| `1 < α < 2` | `ρ^{1-1/α} x` | `1` | `α/(α-1) + k_α` |
| `α = 2` | `x √(ρ L H)` | `1/2` | `3` |
| `α > 2` | `√ρ x` | `min 1 √φ_α` | `α/(α-1) + k_α` |

Here `k_α = √(α K_α/|α - 2|)` with `K_α = 1 + log(max 1 (1/|α - 2|))`, and
`φ_α = α(1 - (1/4)^{1-2/α})/(α - 2)`. -/
noncomputable section
namespace ThresholdHC.PowerQuantileRows
open ThresholdHC.PowerWindow ThresholdHC.CriticalWindow

/-- The rate is comparable with a row once the unclipped terms are. -/
theorem rate_of_row {α ρ x c C Z : ℝ} (hρ : 0 < ρ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hC1 : 1 ≤ C)
    (hrow : powerRow α x ρ = min ρ Z)
    (hsat : powerQuantileScale α ρ ≤ x → ρ ≤ Z)
    (hin : x < powerQuantileScale α ρ →
      c * Z ≤ powerTail α x ρ +
          x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ∧
      powerTail α x ρ +
          x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤ C * Z) :
    c * powerRow α x ρ ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ C * powerRow α x ρ := by
  rw [hrow]
  unfold uniformRate
  by_cases hxs : x < powerQuantileScale α ρ
  · rw [ite_eq_left hxs]
    obtain ⟨hl, hu⟩ := hin hxs
    exact clip_bounds hρ.le hc0.le hc1 hC1 hl hu
  · rw [ite_eq_right hxs, min_eq_left (hsat (le_of_not_gt hxs))]
    constructor <;> nlinarith

theorem scale_cancel {α ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (1 - 1/α) * powerQuantileScale α ρ = ρ := by
  unfold powerQuantileScale
  rw [← Real.rpow_add hρ, show 1 - 1/α + 1/α = 1 by ring, Real.rpow_one]

theorem rpow_le_sqrt {α ρ : ℝ} (hα2 : 2 ≤ α) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ (1 - 1/α) ≤ Real.sqrt ρ := by
  have hα : 0 < α := by linarith
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_ge hρ hρ1
  have : 1/α ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hα2
  linarith

theorem rpow_half_eq {ρ : ℝ} : ρ ^ ((1 : ℝ) - 1/2) = Real.sqrt ρ := by
  rw [Real.sqrt_eq_rpow]
  norm_num

theorem powerRow_two (x ρ : ℝ) :
    powerRow 2 x ρ =
      min ρ (x * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ)) := by
  unfold powerRow
  rw [ite_eq_right (show ¬ (2 : ℝ) < 1 by norm_num), ite_eq_right (show ¬ (2 : ℝ) = 1 by norm_num),
    ite_eq_right (show ¬ (2 : ℝ) < 2 by norm_num), ite_eq_left (show (2 : ℝ) = 2 from rfl)]

/-- Exponents below one: the row `min{ρ, x^α}`. -/
theorem rate_lt_one {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ρ x : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < x →
      c * powerRow α x ρ ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ C * powerRow α x ρ := by
  set k := Real.sqrt (α * (1 + Real.log (max 1 (1 / |α - 2|))) / (2 - α)) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have h1 : 0 < 1 - α := by linarith
  have hC1 : 1 ≤ 1 / (1 - α) + k := by
    have : 1 ≤ 1 / (1 - α) := by rw [le_div_iff₀ h1]; linarith
    linarith
  refine ⟨1, 1 / (1 - α) + k, one_pos, by linarith, ?_⟩
  intro ρ x hρ hρ4 hx
  have hρ1 : ρ < 1 := by linarith
  apply rate_of_row (Z := x ^ α) hρ one_pos le_rfl hC1
  · unfold powerRow
    rw [ite_eq_left hα1]
  · intro hsx
    calc ρ = powerQuantileScale α ρ ^ α := by
          rw [scale_rpow hρ, div_self hα.ne', Real.rpow_one]
      _ ≤ x ^ α := Real.rpow_le_rpow (quantile_scale_pos hρ).le hsx hα.le
  · intro hxs
    have hT := tail_lower_lt_one hα hα1 hρ hx hxs
    have hTu := tail_upper_lt_one hα hα1 hρ hx
    have hY := root_upper_lt_two hα (by linarith) hρ hρ1 hx
    rw [← hk] at hY
    have hc := cross_le_of_le_one hα hα1.le hρ hx hxs.le
    have hY0 : 0 ≤ x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) :=
      mul_nonneg hx.le (Real.sqrt_nonneg _)
    have hkc : k * (ρ ^ (1 - 1/α) * x) ≤ k * x ^ α := mul_le_mul_of_nonneg_left hc hk0
    constructor
    · linarith
    · rw [add_mul]
      linarith

/-- Exponent one: the row `min{ρ, x(1 + log₊(ρ/x))}`. -/
theorem rate_one :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ρ x : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < x →
      c * powerRow 1 x ρ ≤ uniformRate 1 x ρ ∧ uniformRate 1 x ρ ≤ C * powerRow 1 x ρ := by
  set k := Real.sqrt (1 * (1 + Real.log (max 1 (1 / |(1 : ℝ) - 2|))) / (2 - 1)) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  refine ⟨1, 1 + k, one_pos, by linarith, ?_⟩
  intro ρ x hρ hρ4 hx
  have hρ1 : ρ < 1 := by linarith
  have hm0 := le_max_left (0 : ℝ) (Real.log (ρ / x))
  apply rate_of_row (Z := x * (1 + max 0 (Real.log (ρ / x)))) hρ one_pos le_rfl (by linarith)
  · unfold powerRow
    rw [ite_eq_right (lt_irrefl (1 : ℝ)), ite_eq_left rfl]
  · intro hsx
    rw [scale_one] at hsx
    nlinarith
  · intro hxs
    rw [scale_one] at hxs
    have hl : 0 < Real.log (ρ / x) := Real.log_pos ((one_lt_div hx).2 hxs)
    rw [max_eq_right hl.le, tail_one hρ hx]
    have hY := root_upper_lt_two (by norm_num : (0 : ℝ) < 1) (by norm_num) hρ hρ1 hx
    rw [← hk, show (1 : ℝ) - 1/1 = 0 by norm_num, Real.rpow_zero, one_mul] at hY
    have hY0 : 0 ≤ x * Real.sqrt (ρ * powerPhi 1 ρ * (1 + Real.log (effectiveScales 1 ρ))) :=
      mul_nonneg hx.le (Real.sqrt_nonneg _)
    have hxZ : x ≤ x * (1 + Real.log (ρ / x)) := by nlinarith
    have hkx : k * x ≤ k * (x * (1 + Real.log (ρ / x))) := mul_le_mul_of_nonneg_left hxZ hk0
    constructor
    · linarith
    · rw [add_mul, one_mul]
      linarith

/-- Exponents strictly between one and two: the row `min{ρ, ρ^{1-1/α} x}`. -/
theorem rate_between {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ρ x : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < x →
      c * powerRow α x ρ ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ C * powerRow α x ρ := by
  have hα : 0 < α := by linarith
  set k := Real.sqrt (α * (1 + Real.log (max 1 (1 / |α - 2|))) / (2 - α)) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have h1 : 0 < α - 1 := by linarith
  have hC1 : 1 ≤ α / (α - 1) + k := by
    have : 1 ≤ α / (α - 1) := by rw [le_div_iff₀ h1]; linarith
    linarith
  refine ⟨1, α / (α - 1) + k, one_pos, by linarith, ?_⟩
  intro ρ x hρ hρ4 hx
  have hρ1 : ρ < 1 := by linarith
  have hP0 : 0 ≤ ρ ^ (1 - 1/α) := Real.rpow_nonneg hρ.le _
  apply rate_of_row (Z := ρ ^ (1 - 1/α) * x) hρ one_pos le_rfl hC1
  · unfold powerRow
    rw [ite_eq_right (not_lt.2 hα1.le), ite_eq_right (ne_of_gt hα1), ite_eq_left hα2]
  · intro hsx
    calc ρ = ρ ^ (1 - 1/α) * powerQuantileScale α ρ := (scale_cancel hρ).symm
      _ ≤ ρ ^ (1 - 1/α) * x := mul_le_mul_of_nonneg_left hsx hP0
  · intro hxs
    have hT := tail_lower_gt_one hα1 hρ hx hxs
    have hTu := tail_upper_gt_one hα1 hρ hx
    have hY := root_upper_lt_two hα hα2 hρ hρ1 hx
    rw [← hk] at hY
    have hY0 : 0 ≤ x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) :=
      mul_nonneg hx.le (Real.sqrt_nonneg _)
    constructor
    · linarith
    · rw [add_mul]
      linarith

/-- Exponent two: the row `min{ρ, x √(ρ L H)}`. -/
theorem rate_two :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ρ x : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < x →
      c * powerRow 2 x ρ ≤ uniformRate 2 x ρ ∧ uniformRate 2 x ρ ≤ C * powerRow 2 x ρ := by
  refine ⟨1/2, 3, by norm_num, by norm_num, ?_⟩
  intro ρ x hρ hρ4 hx
  have hρ1 : ρ < 1 := by linarith
  have hcrit := critical_factor_ge_one hρ hρ4
  have hroot : Real.sqrt ρ ≤
      Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_right hρ.le hcrit)
  have hs0 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  apply rate_of_row (Z := x * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ))
    hρ (by norm_num) (by norm_num) (by norm_num) (powerRow_two x ρ)
  · intro hsx
    have hc := scale_cancel (α := 2) hρ
    rw [rpow_half_eq] at hc
    calc ρ = Real.sqrt ρ * powerQuantileScale 2 ρ := hc.symm
      _ ≤ Real.sqrt ρ * x := mul_le_mul_of_nonneg_left hsx hs0
      _ ≤ x * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hroot hx.le
  · intro hxs
    have hT := power_tail_nonneg (by norm_num : (0 : ℝ) < 2) hx hxs
    have hTu := tail_upper_gt_one (by norm_num : (1 : ℝ) < 2) hρ hx
    rw [rpow_half_eq, show (2 : ℝ) / (2 - 1) = 2 by norm_num] at hTu
    obtain ⟨hYl, hYu⟩ := quadratic_root_bounds hρ hρ4 hx
    have hxs' : Real.sqrt ρ * x ≤
        x * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hroot hx.le
    constructor
    · linarith
    · linarith

/-- Exponents above two: the row `min{ρ, √ρ x}`. -/
theorem rate_gt_two {α : ℝ} (hα2 : 2 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ρ x : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < x →
      c * powerRow α x ρ ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ C * powerRow α x ρ := by
  have hα : 0 < α := by linarith
  have hα1 : 1 < α := by linarith
  set k := Real.sqrt (α * (1 + Real.log (max 1 (1 / |α - 2|))) / (α - 2)) with hk
  set q := Real.sqrt (α * (1 - (1/4 : ℝ) ^ (1 - 2/α)) / (α - 2)) with hq
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hq0 : 0 < q := Real.sqrt_pos.2 (phi_const_pos hα2)
  have h1 : 0 < α - 1 := by linarith
  have hA : 1 ≤ α / (α - 1) := by rw [le_div_iff₀ h1]; linarith
  have hC1 : 1 ≤ α / (α - 1) + k := by linarith
  refine ⟨min 1 q, α / (α - 1) + k, lt_min one_pos hq0, by linarith, ?_⟩
  intro ρ x hρ hρ4 hx
  have hρ1 : ρ < 1 := by linarith
  have hP0 : 0 ≤ ρ ^ (1 - 1/α) := Real.rpow_nonneg hρ.le _
  have hPs := rpow_le_sqrt hα2.le hρ hρ1.le
  have hZ0 : 0 ≤ Real.sqrt ρ * x := mul_nonneg (Real.sqrt_nonneg ρ) hx.le
  apply rate_of_row (Z := Real.sqrt ρ * x) hρ (lt_min one_pos hq0) (min_le_left _ _) hC1
  · unfold powerRow
    rw [ite_eq_right (not_lt.2 hα1.le), ite_eq_right (ne_of_gt hα1),
      ite_eq_right (not_lt.2 hα2.le), ite_eq_right hα2.ne']
  · intro hsx
    calc ρ = ρ ^ (1 - 1/α) * powerQuantileScale α ρ := (scale_cancel hρ).symm
      _ ≤ ρ ^ (1 - 1/α) * x := mul_le_mul_of_nonneg_left hsx hP0
      _ ≤ Real.sqrt ρ * x := mul_le_mul_of_nonneg_right hPs hx.le
  · intro hxs
    have hT := power_tail_nonneg hα hx hxs
    have hTu := tail_upper_gt_one hα1 hρ hx
    have hPx : ρ ^ (1 - 1/α) * x ≤ Real.sqrt ρ * x := mul_le_mul_of_nonneg_right hPs hx.le
    have hTu' : α / (α - 1) * (ρ ^ (1 - 1/α) * x) ≤ α / (α - 1) * (Real.sqrt ρ * x) :=
      mul_le_mul_of_nonneg_left hPx (by linarith)
    have hY := root_upper_gt_two hα2 hρ hρ1 hx
    rw [← hk] at hY
    have hYl := root_lower_gt_two hα2 hρ hρ4 hx
    rw [← hq] at hYl
    have hmin : min 1 q * (Real.sqrt ρ * x) ≤ q * (Real.sqrt ρ * x) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hZ0
    constructor
    · linarith
    · rw [add_mul]
      linarith

end ThresholdHC.PowerQuantileRows
