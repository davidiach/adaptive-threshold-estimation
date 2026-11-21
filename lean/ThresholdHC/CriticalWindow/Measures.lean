import ThresholdHC.CriticalWindow.Rate

/-! The risk and `Ψ` statements of Corollary 14.14 (v6 §14.8).

For an exact power law the entropy-free quantile functional `Q⁰` is the window
rate with `K = 1` (`power_quantileZero`). The uniform power-law risk bounds of
`PowerWindow` and the closed form `Q⁰/√2 ≤ Ψ ≤ Q⁰` of `PsiClosedForm` then give
display (W9) with the paper's constants `10^{-18}` and `3.4·10^5`, the `Ψ`
bounds, and the ratio statement. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.CriticalWindow
open ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile ThresholdHC.PsiGap

/-- The entropy-free quantile functional `Q⁰` of an exact power law. -/
theorem power_quantileZero (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a) :
    quantileZero μ ρ B = ENNReal.ofReal (windowRate α (1 / (a * Real.sqrt B)) ρ 1) := by
  set x := 1 / (a * Real.sqrt B) with hxdef
  have hx : 0 < x := by dsimp [x]; positivity
  have hρ1 : ρ < 1 := by linarith
  have hh : 1 / Real.sqrt B = a * x := by rw [hxdef]; field_simp
  have : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1.le)
  obtain ⟨_, hinv, -, -, -⟩ := core_entropy μ ρ hρ hρ4
  have hcost := power_core_cost μ hα ha ha2 hρ hρ1 hm
  have hcore : ENNReal.ofReal (1 / Real.sqrt B) *
      (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ) =
      ENNReal.ofReal (x * Real.sqrt (ρ * powerPhi α ρ * 1)) := by
    rw [hinv, ← ENNReal.ofReal_mul hρ.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hh, ← hcost, mul_one, show ρ * (a^2 * coreCost μ ρ) = a^2 * (ρ * coreCost μ ρ) by ring,
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
    ring
  unfold quantileZero
  rw [hcore, ← ThresholdHC.EntropyTail.quantile_tailModulus_eq _
    (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt B), hh]
  unfold windowRate
  by_cases ht : x < powerQuantileScale α ρ
  · rw [ite_eq_left ht, power_tail_formula μ hα ha ha2 hρ hρ1 hm hx ht,
      ← ENNReal.ofReal_add (power_tail_nonneg hα hx ht) (by positivity), ofReal_minimum]
  · rw [ite_eq_right ht, power_tail_saturated μ hα ha ha2 hρ hρ1 hm (not_lt.1 ht),
      min_eq_left le_self_add]

/-- Corollary 14.14, risk part, with the paper's constants `10^{-18}` and `3.4·10^5`. -/
theorem risk_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a) :
    let Y := 1 / (a * Real.sqrt B) *
      Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ)))
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ Y) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (340000 * min ρ Y) := by
  intro Y
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hx : 0 < 1 / (a * Real.sqrt B) := by positivity
  have hK : 1 ≤ 1 + Real.log (effectiveScales α ρ) := by
    linarith [Real.log_nonneg (effective_scales_ge_one hα hρ hρ1)]
  obtain ⟨hl, hu⟩ := window_rate_bounds hα1 hα3 hρ hρ4 hx hK
  rw [windowRate_entropy] at hl hu
  obtain ⟨hRl, hRu⟩ := power_risk μ α a ρ B hα (by linarith) ha ha2 hρ hρ4 hB hm
  have hm0 : 0 ≤ min ρ Y := le_min hρ.le (by positivity)
  have hs : Real.sqrt 2 ≤ 10 := by
    rw [show (10 : ℝ) = Real.sqrt 100 by
      rw [show (100 : ℝ) = 10^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hRl
    have hc : (10 : ℝ)⁻¹ ^ 18 ≤ (10 : ℝ)⁻¹ ^ 17 / Real.sqrt 2 := by
      rw [le_div_iff₀ hs0]
      have : (10 : ℝ)⁻¹ ^ 18 * 10 = (10 : ℝ)⁻¹ ^ 17 := by norm_num
      nlinarith [pow_pos (show (0 : ℝ) < 10⁻¹ by norm_num) 18]
    have hr0 : 0 ≤ uniformRate α (1 / (a * Real.sqrt B)) ρ := hm0.trans hl
    calc (10 : ℝ)⁻¹ ^ 18 * min ρ Y ≤ (10 : ℝ)⁻¹ ^ 17 / Real.sqrt 2 * min ρ Y :=
          mul_le_mul_of_nonneg_right hc hm0
      _ ≤ (10 : ℝ)⁻¹ ^ 17 / Real.sqrt 2 * uniformRate α (1 / (a * Real.sqrt B)) ρ :=
          mul_le_mul_of_nonneg_left hl (by positivity)
  · refine hRu.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith

/-- Corollary 14.14, `Ψ` part: `min{ρ, Y⁰}/√2 ≤ Ψ ≤ 5.13 min{ρ, Y⁰}`. -/
theorem psi_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a) :
    let Y₀ := 1 / (a * Real.sqrt B) * Real.sqrt (ρ * powerPhi α ρ)
    ENNReal.ofReal (min ρ Y₀ / Real.sqrt 2) ≤ rarePsi μ ρ (1 / Real.sqrt B) ∧
    rarePsi μ ρ (1 / Real.sqrt B) ≤ ENNReal.ofReal ((513/100) * min ρ Y₀) := by
  intro Y₀
  have hα : 0 < α := by linarith
  have hx : 0 < 1 / (a * Real.sqrt B) := by positivity
  obtain ⟨hl, hu⟩ := window_rate_bounds hα1 hα3 hρ hρ4 hx (le_refl (1 : ℝ))
  rw [mul_one] at hl hu
  have hQ := power_quantileZero μ hα ha ha2 hρ hρ4 hB hm
  obtain ⟨h1, h2, h3⟩ := psi_closed_form μ ρ B hρ hρ4 hB
  have hs0 : 0 < Real.sqrt 2 := by positivity
  constructor
  · calc ENNReal.ofReal (min ρ Y₀ / Real.sqrt 2)
        ≤ ENNReal.ofReal (windowRate α (1 / (a * Real.sqrt B)) ρ 1 / Real.sqrt 2) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hl hs0.le)
      _ = quantileZero μ ρ B / ENNReal.ofReal (Real.sqrt 2) := by
          rw [hQ, ENNReal.ofReal_div_of_pos hs0]
      _ ≤ rarePsi μ ρ (1 / Real.sqrt B) := by
          apply ENNReal.div_le_of_le_mul
          rw [mul_comm]; exact h1
  · calc rarePsi μ ρ (1 / Real.sqrt B) ≤ quantileZero μ ρ B := h2.trans h3
      _ = ENNReal.ofReal (windowRate α (1 / (a * Real.sqrt B)) ρ 1) := hQ
      _ ≤ ENNReal.ofReal ((513/100) * min ρ Y₀) := ENNReal.ofReal_le_ofReal hu

/-- Corollary 14.14, last sentence: when `Y ≤ ρ`, the ratio of the minimax risk to `Ψ`
lies between universal multiples of `√(1 + log N_α(ρ))`. -/
theorem ratio_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a)
    (hYρ : 1 / (a * Real.sqrt B) *
      Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤ ρ) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 19 * Real.sqrt (1 + Real.log (effectiveScales α ρ))) *
        rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤
      ENNReal.ofReal (500000 * Real.sqrt (1 + Real.log (effectiveScales α ρ))) *
        rarePsi μ ρ (1 / Real.sqrt B) := by
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  set x := 1 / (a * Real.sqrt B) with hxdef
  have hx : 0 < x := by dsimp [x]; positivity
  set K := 1 + Real.log (effectiveScales α ρ) with hKdef
  have hK : 1 ≤ K := by linarith [Real.log_nonneg (effective_scales_ge_one hα hρ hρ1)]
  have hphi0 : 0 ≤ ρ * powerPhi α ρ := mul_nonneg hρ.le (power_phi_pos hα hρ hρ1).le
  set Y₀ := x * Real.sqrt (ρ * powerPhi α ρ) with hY0def
  have hY0 : 0 ≤ Y₀ := by positivity
  have hsK : 1 ≤ Real.sqrt K := Real.one_le_sqrt.2 hK
  have hYeq : x * Real.sqrt (ρ * powerPhi α ρ * K) = Real.sqrt K * Y₀ := by
    rw [Real.sqrt_mul hphi0 K, hY0def]; ring
  rw [hYeq] at hYρ
  have hY0ρ : Y₀ ≤ ρ := le_trans (le_mul_of_one_le_left hY0 hsK) hYρ
  obtain ⟨hRl, hRu⟩ := risk_bounds μ hα1 hα3 ha ha2 hρ hρ4 hB hm
  obtain ⟨hPl, hPu⟩ := psi_bounds μ hα1 hα3 ha ha2 hρ hρ4 hB hm
  rw [← hxdef, ← hKdef, hYeq, min_eq_right hYρ] at hRl hRu
  rw [← hxdef, ← hY0def, min_eq_right hY0ρ] at hPl hPu
  have hsK0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  constructor
  · calc ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 19 * Real.sqrt K) * rarePsi μ ρ (1 / Real.sqrt B)
        ≤ ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 19 * Real.sqrt K) * ENNReal.ofReal ((513/100) * Y₀) :=
          by gcongr
      _ = ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 19 * Real.sqrt K * ((513/100) * Y₀)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * (Real.sqrt K * Y₀)) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : (10 : ℝ)⁻¹ ^ 19 * (513/100) ≤ (10 : ℝ)⁻¹ ^ 18 := by norm_num
          have h2 : 0 ≤ Real.sqrt K * Y₀ := by positivity
          nlinarith
      _ ≤ rareMinimaxRisk μ ρ B := hRl
  · have hs := sqrt_two_le
    have hs0 : 0 < Real.sqrt 2 := by positivity
    calc rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (340000 * (Real.sqrt K * Y₀)) := hRu
      _ ≤ ENNReal.ofReal (500000 * Real.sqrt K * (Y₀ / Real.sqrt 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_div_assoc', le_div_iff₀ hs0]
          have h2 : 0 ≤ Real.sqrt K * Y₀ := by positivity
          nlinarith
      _ = ENNReal.ofReal (500000 * Real.sqrt K) * ENNReal.ofReal (Y₀ / Real.sqrt 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (500000 * Real.sqrt K) * rarePsi μ ρ (1 / Real.sqrt B) :=
          by gcongr


end ThresholdHC.CriticalWindow
