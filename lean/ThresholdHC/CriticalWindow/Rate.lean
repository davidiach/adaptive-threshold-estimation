import ThresholdHC.PowerWindow.Full
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The deterministic part of Corollary 14.14 (v6 §14.8).

On the window `3/2 ≤ α ≤ 3`, `ρ Φ_α(ρ) ≥ (53/100) ρ^{2-2/α}` (`rho_phi_lower`), so
`√(ρ Φ_α(ρ)) ≥ 0.728 ρ^{1-1/α}`; below the quantile scale the power-law tail is
at most `3 x ρ^{1-1/α}` (`power_tail_upper`), hence at most `4.13 Y`. This gives
`min{ρ, Y} ≤ R_α(x, ρ) ≤ 5.13 min{ρ, Y}` for every entropy factor `K ≥ 1`
(`window_rate_bounds`); `K = 1 + log N_α(ρ)` is the rate (W7) and `K = 1` its
entropy-free form. The module also collects the elementary bounds used by
`Remark`. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.CriticalWindow
open ThresholdHC.PowerWindow

theorem rpow_sq_two_sub {α ρ : ℝ} (hρ : 0 < ρ) :
    (ρ ^ (1 - 1/α))^2 = ρ ^ (2 - 2/α) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  congr 1; push_cast; ring

theorem scale_rpow {α ρ r : ℝ} (hρ : 0 < ρ) :
    powerQuantileScale α ρ ^ r = ρ ^ (r / α) := by
  unfold powerQuantileScale
  rw [← Real.rpow_mul hρ.le]
  congr 1; ring

theorem rpow_interval_integrable {r a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => t ^ r) volume a b := by
  apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
  rcases le_total a b with h | h
  · exact notMem_uIcc_of_lt ha (ha.trans_le h)
  · exact notMem_uIcc_of_lt (hb.trans_le h) hb

theorem sqrt_two_le : Real.sqrt 2 ≤ 14144 / 10000 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem two_rpow_lower {α : ℝ} (hα1 : 3/2 ≤ α) : (53/100 : ℝ) ≤ α * 2 ^ (α - 3) := by
  have hmono : (2 : ℝ) ^ (-(3/2 : ℝ)) ≤ 2 ^ (α - 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hval : (2 : ℝ) ^ (-(3/2 : ℝ)) = (2 * Real.sqrt 2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hs := sqrt_two_le
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hbase : (53/100 : ℝ) ≤ (3/2) * (2 * Real.sqrt 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith
  calc (53/100 : ℝ) ≤ (3/2) * (2 * Real.sqrt 2)⁻¹ := hbase
    _ ≤ α * 2 ^ (α - 3) := by
      rw [← hval]
      exact mul_le_mul hα1 hmono (by positivity) (by linarith)

theorem cube_root_quarter : ((1/4 : ℝ)) ^ (1/3 : ℝ) ≤ 63/100 := by
  rw [show (1/3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1/4)
    (show (1/4 : ℝ) ≤ (63/100)^3 by norm_num) (by positivity : (0 : ℝ) ≤ ((3 : ℕ) : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at h

/-- `ρ Φ_α(ρ) ≥ (53/100) ρ^{2-2/α}` on the window `3/2 ≤ α ≤ 3`. -/
theorem rho_phi_lower {α ρ : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    (53/100 : ℝ) * ρ ^ (2 - 2/α) ≤ ρ * powerPhi α ρ := by
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hs : 0 < powerQuantileScale α ρ := quantile_scale_pos hρ
  have hs1 : powerQuantileScale α ρ < 1 := quantile_scale_lt_one hα hρ hρ1
  have hρ2 : ρ * ρ ^ (1 - 2/α) = ρ ^ (2 - 2/α) := by
    rw [show (2 : ℝ) - 2/α = 1 + (1 - 2/α) by ring, Real.rpow_add hρ, Real.rpow_one]
  by_cases h2 : α ≤ 2
  · set s := powerQuantileScale α ρ with hsdef
    have hs2 : 2 * s ≤ 1 := by
      have h1 : s ≤ ρ ^ (1/2 : ℝ) := by
        rw [hsdef]; unfold powerQuantileScale
        exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le
          (by rw [div_le_div_iff₀ (by norm_num) hα]; linarith)
      have h12 : ρ ^ (1/2 : ℝ) ≤ 1/2 := by
        rw [← Real.sqrt_eq_rpow]
        rw [show (1/2 : ℝ) = Real.sqrt (1/4) by
          rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hρ4
      linarith
    have hsub : (∫ t in s..2*s, t ^ (α - 3)) ≤ ∫ t in s..1, t ^ (α - 3) :=
      intervalIntegral.integral_mono_interval le_rfl (by linarith) hs2
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
          (fun t ht => Real.rpow_nonneg (hs.trans ht.1).le _)))
        (rpow_interval_integrable hs (by norm_num))
    have hconst : (∫ t in s..2*s, (2*s) ^ (α - 3)) ≤ ∫ t in s..2*s, t ^ (α - 3) := by
      apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (rpow_interval_integrable hs (by linarith))
      intro t ht
      exact Real.rpow_le_rpow_of_nonpos (hs.trans_le ht.1) ht.2 (by linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hconst
    have e1 : s * s ^ (α - 3) = s ^ (α - 2) := by
      rw [show α - 2 = 1 + (α - 3) by ring, Real.rpow_add hs, Real.rpow_one]
    have e2 : s ^ (α - 2) = ρ ^ (1 - 2/α) := by
      rw [hsdef, scale_rpow hρ, sub_div, div_self hα.ne']
    have hval : (2*s - s) * (2*s) ^ (α - 3) = 2 ^ (α - 3) * ρ ^ (1 - 2/α) := by
      rw [Real.mul_rpow (by norm_num) hs.le, ← e2, ← e1]
      ring
    have hphi : α * (2 ^ (α - 3) * ρ ^ (1 - 2/α)) ≤ powerPhi α ρ := by
      unfold powerPhi
      rw [← hsdef]
      exact mul_le_mul_of_nonneg_left (by linarith) hα.le
    calc (53/100 : ℝ) * ρ ^ (2 - 2/α) ≤ (α * 2 ^ (α - 3)) * ρ ^ (2 - 2/α) :=
          mul_le_mul_of_nonneg_right (two_rpow_lower hα1) (by positivity)
      _ = ρ * (α * (2 ^ (α - 3) * ρ ^ (1 - 2/α))) := by rw [← hρ2]; ring
      _ ≤ ρ * powerPhi α ρ := mul_le_mul_of_nonneg_left hphi hρ.le
  · have h2' : 2 < α := lt_of_not_ge h2
    have hint : (1 - powerQuantileScale α ρ) ≤ ∫ t in powerQuantileScale α ρ..1, t ^ (α - 3) := by
      have := intervalIntegral.integral_mono_on hs1.le
        (intervalIntegrable_const (c := (1 : ℝ)))
        (rpow_interval_integrable (r := α - 3) hs (by norm_num))
        (fun t ht => Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hs.trans_le ht.1) ht.2
          (by linarith))
      simpa using this
    have hs63 : powerQuantileScale α ρ ≤ 63/100 := by
      unfold powerQuantileScale
      calc ρ ^ (1/α) ≤ ρ ^ (1/3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le
            (one_div_le_one_div_of_le hα hα3)
        _ ≤ (1/4 : ℝ) ^ (1/3 : ℝ) := Real.rpow_le_rpow hρ.le hρ4 (by norm_num)
        _ ≤ 63/100 := cube_root_quarter
    have hphi : (74/100 : ℝ) ≤ powerPhi α ρ := by
      unfold powerPhi
      nlinarith
    have hpow : ρ ^ (2 - 2/α) ≤ ρ := by
      have := Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le
        (show (1 : ℝ) ≤ 2 - 2/α by
          have : 2/α ≤ 1 := by rw [div_le_one hα]; linarith
          linarith)
      simpa using this
    nlinarith

/-- For `x` below the quantile scale, `T_α(x, ρ) ≤ 3 x ρ^{1-1/α}` when `α ≥ 3/2`. -/
theorem power_tail_upper {α x ρ : ℝ} (hα1 : 3/2 ≤ α) (hρ : 0 < ρ) (hx : 0 < x) :
    powerTail α x ρ ≤ 3 * x * ρ ^ (1 - 1/α) := by
  have hα : 0 < α := by linarith
  set s := powerQuantileScale α ρ with hsdef
  have hint : (∫ t in x..s, t ^ (α - 2)) = (s ^ (α - 1) - x ^ (α - 1)) / (α - 1) := by
    rw [integral_rpow (Or.inl (by linarith))]
    rw [show α - 2 + 1 = α - 1 by ring]
  have hS : s ^ (α - 1) = ρ ^ (1 - 1/α) := by
    rw [hsdef, scale_rpow hρ, sub_div, div_self hα.ne']
  have hxa : x ^ α = x * x ^ (α - 1) := by
    rw [show α = 1 + (α - 1) by ring, Real.rpow_add hx, Real.rpow_one]
    congr 2; ring
  have hA : 0 ≤ x ^ (α - 1) := Real.rpow_nonneg hx.le _
  have hα1' : 0 < α - 1 := by linarith
  unfold powerTail
  rw [← hsdef, hint, hxa, ← hS]
  have hkey : x * x ^ (α - 1) + α * x * ((s ^ (α - 1) - x ^ (α - 1)) / (α - 1)) =
      (α * x * s ^ (α - 1) - x * x ^ (α - 1)) / (α - 1) := by
    field_simp; ring
  rw [hkey, div_le_iff₀ hα1']
  have hS0 : 0 ≤ s ^ (α - 1) := Real.rpow_nonneg (quantile_scale_pos hρ).le _
  nlinarith [mul_nonneg hx.le hA, mul_nonneg hx.le hS0]

theorem power_tail_nonneg {α x ρ : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hxs : x < powerQuantileScale α ρ) : 0 ≤ powerTail α x ρ := by
  unfold powerTail
  have hi : 0 ≤ ∫ t in x..powerQuantileScale α ρ, t ^ (α - 2) :=
    intervalIntegral.integral_nonneg hxs.le (fun t ht => Real.rpow_nonneg (hx.le.trans ht.1) _)
  have := Real.rpow_nonneg hx.le α
  positivity

/-- `0.728 ρ^{1-1/α} ≤ √(ρ Φ_α(ρ))` on the window. -/
theorem root_phi_lower {α ρ : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    (728/1000 : ℝ) * ρ ^ (1 - 1/α) ≤ Real.sqrt (ρ * powerPhi α ρ) := by
  have h := rho_phi_lower hα1 hα3 hρ hρ4
  rw [← rpow_sq_two_sub (α := α) hρ] at h
  apply Real.le_sqrt_of_sq_le
  have hp : 0 ≤ (ρ ^ (1 - 1/α))^2 := sq_nonneg _
  nlinarith

/-- The rate of (W7) with the entropy factor `1 + log N` replaced by any `K ≥ 1`. -/
def windowRate (α x ρ K : ℝ) : ℝ :=
  if x < powerQuantileScale α ρ then
    min ρ (powerTail α x ρ + x * Real.sqrt (ρ * powerPhi α ρ * K))
  else ρ

theorem windowRate_entropy (α x ρ : ℝ) :
    windowRate α x ρ (1 + Real.log (effectiveScales α ρ)) = uniformRate α x ρ := rfl

/-- The deterministic part of Corollary 14.14, for any entropy factor `K ≥ 1`. -/
theorem window_rate_bounds {α ρ x K : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hx : 0 < x) (hK : 1 ≤ K) :
    min ρ (x * Real.sqrt (ρ * powerPhi α ρ * K)) ≤ windowRate α x ρ K ∧
    windowRate α x ρ K ≤ (513/100) * min ρ (x * Real.sqrt (ρ * powerPhi α ρ * K)) := by
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  set Y := x * Real.sqrt (ρ * powerPhi α ρ * K) with hY
  have hphi0 : 0 ≤ ρ * powerPhi α ρ := mul_nonneg hρ.le (power_phi_pos hα hρ hρ1).le
  have hY0 : x * Real.sqrt (ρ * powerPhi α ρ) ≤ Y := by
    rw [hY]
    apply mul_le_mul_of_nonneg_left _ hx.le
    exact Real.sqrt_le_sqrt (le_mul_of_one_le_right hphi0 hK)
  have hroot := root_phi_lower hα1 hα3 hρ hρ4
  have hP : 0 ≤ ρ ^ (1 - 1/α) := Real.rpow_nonneg hρ.le _
  have hYlow : (728/1000 : ℝ) * x * ρ ^ (1 - 1/α) ≤ Y := by
    calc (728/1000 : ℝ) * x * ρ ^ (1 - 1/α) = x * ((728/1000 : ℝ) * ρ ^ (1 - 1/α)) := by ring
      _ ≤ x * Real.sqrt (ρ * powerPhi α ρ) := mul_le_mul_of_nonneg_left hroot hx.le
      _ ≤ Y := hY0
  unfold windowRate
  rw [← hY]
  by_cases hxs : x < powerQuantileScale α ρ
  · rw [ite_eq_left hxs]
    have hT := power_tail_nonneg hα hx hxs
    have hTu := power_tail_upper hα1 hρ hx (α := α)
    have hTY : powerTail α x ρ ≤ (413/100) * Y := by nlinarith
    constructor
    · exact min_le_min le_rfl (by linarith)
    · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 513/100)]
      exact min_le_min (by linarith) (by linarith)
  · rw [ite_eq_right hxs]
    push Not at hxs
    have hs := quantile_scale_pos (α := α) hρ
    have hcancel : powerQuantileScale α ρ * ρ ^ (1 - 1/α) = ρ := by
      unfold powerQuantileScale
      rw [← Real.rpow_add hρ, show 1/α + (1 - 1/α) = 1 by ring, Real.rpow_one]
    have hYρ : (728/1000 : ℝ) * ρ ≤ Y := by
      calc (728/1000 : ℝ) * ρ = (728/1000 : ℝ) * (powerQuantileScale α ρ * ρ ^ (1 - 1/α)) := by
            rw [hcancel]
        _ ≤ (728/1000 : ℝ) * x * ρ ^ (1 - 1/α) := by
            nlinarith [mul_le_mul_of_nonneg_right hxs hP]
        _ ≤ Y := hYlow
    constructor
    · exact min_le_left _ _
    · rcases le_total ρ Y with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith

theorem mul_sqrt_eq {c X : ℝ} (hc : 0 ≤ c) : c * Real.sqrt X = Real.sqrt (c^2 * X) := by
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem log_inv_ge_one {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) : 1 ≤ Real.log (1/ρ) := by
  have h4 : (4 : ℝ) ≤ 1/ρ := by rw [le_div_iff₀ hρ]; linarith
  have hl4 : Real.log 4 ≤ Real.log (1/ρ) := Real.log_le_log (by norm_num) h4
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9]

theorem abs_one_sub_two_div {α : ℝ} (hα : 0 < α) : |1 - 2/α| = |α - 2| / α := by
  rw [show 1 - 2/α = (α - 2) / α by field_simp, abs_div, abs_of_pos hα]

theorem rpow_exp_form {ρ c : ℝ} (hρ : 0 < ρ) : ρ ^ c = Real.exp (-(c * Real.log (1/ρ))) := by
  rw [Real.rpow_def_of_pos hρ, one_div, Real.log_inv]; ring_nf

theorem exp_two_thirds_le : Real.exp (2/3) ≤ 2 := by
  have h3 : Real.exp (2/3) ^ 3 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (2/3)
  by_contra h
  push Not at h
  have h8 : (8 : ℝ) < Real.exp (2/3) ^ 3 := by
    nlinarith [mul_pos (sub_pos.2 h) (by positivity : (0:ℝ) < Real.exp (2/3) ^ 2 + 2 * Real.exp (2/3) + 4)]
  have he2 : Real.exp 1 ^ 2 < 8 := by
    nlinarith [mul_pos (sub_pos.2 he) (by positivity : (0:ℝ) < 2.7182818286 + Real.exp 1)]
  linarith

end ThresholdHC.CriticalWindow
