import ThresholdHC.PowerWindow.TailIntegral
import ThresholdHC.PowerWindow.CoreCost
import ThresholdHC.PsiGap.Full

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiGap
open ThresholdHC.EntropyTailQuantile

theorem effective_scales_ge_one {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    1 ≤ effectiveScales α ρ := by
  have hl : 0 ≤ Real.logb 2 (1 / ρ) :=
    Real.logb_nonneg (by norm_num) ((one_le_div hρ).2 hρ1.le)
  unfold effectiveScales
  split_ifs
  · linarith [div_nonneg hl (by norm_num : (0 : ℝ) ≤ 2)]
  · exact le_min (by linarith [div_nonneg hl hα.le]) (le_max_left _ _)

theorem power_core_term (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a) :
    ENNReal.ofReal (1 / Real.sqrt B) *
      (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ) =
    ENNReal.ofReal ((1 / (a * Real.sqrt B)) *
      Real.sqrt (ρ * powerPhi α ρ * (1 + coreEntropy μ ρ))) := by
  obtain ⟨hA, _, hE, hΓ, _⟩ := core_entropy μ ρ hρ hρ4
  have hcost := power_core_cost μ hα ha ha2 hρ (by linarith) hm
  rw [hΓ, ← ENNReal.ofReal_mul hρ.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← hcost, show ρ * (a^2 * coreCost μ ρ) * (1 + coreEntropy μ ρ) =
    a^2 * (ρ * (coreCost μ ρ * (1 + coreEntropy μ ρ))) by ring,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  field_simp

theorem ofReal_minimum (x y : ℝ) :
    min (ENNReal.ofReal x) (ENNReal.ofReal y) = ENNReal.ofReal (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (ENNReal.ofReal_le_ofReal h)]
  · rw [min_eq_right h, min_eq_right (ENNReal.ofReal_le_ofReal h)]

/-- The quantile functional itself, including its saturated branch. -/
theorem power_quantile_formula (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a) :
    let x := 1 / (a * Real.sqrt B)
    closedQuantileValue μ ρ B = ENNReal.ofReal
      (if x < powerQuantileScale α ρ then
        min ρ (powerTail α x ρ + x * Real.sqrt (ρ * powerPhi α ρ * (1 + coreEntropy μ ρ)))
      else ρ) := by
  dsimp only
  set x := 1 / (a * Real.sqrt B) with hxdef
  have hx : 0 < x := by dsimp [x]; positivity
  have hρ1 : ρ < 1 := by linarith
  have hh : 1 / Real.sqrt B = a * x := by rw [hxdef]; field_simp
  unfold closedQuantileValue ThresholdHC.EntropyTailQuantile.budgetScale
  rw [show (Real.sqrt B)⁻¹ = 1 / Real.sqrt B by exact (one_div _).symm,
    power_core_term μ hα ha ha2 hρ hρ4 hB hm]
  change min (ENNReal.ofReal ρ)
    (ENNReal.ofReal (tailModulus (quantileTail μ ρ) (1 / Real.sqrt B)) +
      ENNReal.ofReal (x * Real.sqrt (ρ * powerPhi α ρ * (1 + coreEntropy μ ρ)))) = _
  by_cases ht : x < powerQuantileScale α ρ
  · have htail : tailModulus (quantileTail μ ρ) (1 / Real.sqrt B) = powerTail α x ρ := by
      rw [hh]
      exact power_tail_formula μ hα ha ha2 hρ hρ1 hm hx ht
    have hT : 0 ≤ powerTail α x ρ := by
      rw [← htail]
      apply integral_nonneg
      intro d
      exact le_min (by norm_num) (div_nonneg (by positivity) d.2.1.le)
    rw [ite_eq_left ht, htail, ← ENNReal.ofReal_add hT (by positivity), ofReal_minimum]
  · have htail : tailModulus (quantileTail μ ρ) (1 / Real.sqrt B) = ρ := by
      rw [hh]
      exact power_tail_saturated μ hα ha ha2 hρ hρ1 hm (not_lt.1 ht)
    rw [ite_eq_right ht, htail, min_eq_left le_self_add]

theorem clipped_sum_comparison {ρ T U V : ℝ} (hρ : 0 ≤ ρ) (hT : 0 ≤ T)
    (hl : U / Real.sqrt 2 ≤ V) (hu : V ≤ 2 * U) :
    min ρ (T + U) / Real.sqrt 2 ≤ min ρ (T + V) ∧
    min ρ (T + V) ≤ 2 * min ρ (T + U) := by
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have hs0 : (0 : ℝ) < Real.sqrt 2 := by positivity
  constructor
  · rw [← min_div_div_right hs0.le]
    apply min_le_min
    · exact div_le_self hρ hs
    · rw [add_div]
      exact add_le_add (div_le_self hT hs) hl
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact min_le_min (by linarith) (by linarith)

theorem core_root_comparison {C K E x : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hl : (1/2 : ℝ) * K ≤ E) (hu : E ≤ (383/100 : ℝ) * K) :
    x * Real.sqrt (C * K) / Real.sqrt 2 ≤ x * Real.sqrt (C * E) ∧
    x * Real.sqrt (C * E) ≤ 2 * (x * Real.sqrt (C * K)) := by
  have hlo : C * K / 2 ≤ C * E := by nlinarith [mul_le_mul_of_nonneg_left hl hC]
  have hhi : C * E ≤ 4 * (C * K) := by
    nlinarith [mul_le_mul_of_nonneg_left hu hC, mul_nonneg hC hK]
  constructor
  · have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo) hx
    rw [Real.sqrt_div (mul_nonneg hC hK)] at hs
    simpa only [mul_div_assoc] using hs
  · have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhi) hx
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hs
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
    rw [hs4] at hs
    nlinarith

/-- The deterministic comparison follows from the uniform core entropy target.
This implication will be applied to the proved entropy estimate. -/
theorem power_quantile_of_core (hcore : PowerCoreStatement) : PowerQuantileStatement := by
  intro μ _ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm
  have hρ1 : ρ < 1 := by linarith
  set x := 1 / (a * Real.sqrt B) with hxdef
  have hx : 0 < x := by dsimp [x]; positivity
  have hN := effective_scales_ge_one hα hρ hρ1
  have hK : 0 ≤ 1 + Real.log (effectiveScales α ρ) := by linarith [Real.log_nonneg hN]
  obtain ⟨_, hlo, hhi⟩ := hcore μ α a ρ hα hα4 ha ha2 hρ hρ1 hm
  have hC : 0 ≤ ρ * powerPhi α ρ := mul_nonneg hρ.le (power_phi_pos hα hρ hρ1).le
  obtain ⟨hl, hu⟩ := core_root_comparison hC hK hx.le hlo hhi
  rw [power_quantile_formula μ hα ha ha2 hρ hρ4 hB hm]
  rw [← hxdef]
  change ENNReal.ofReal (uniformRate α x ρ / Real.sqrt 2) ≤ _ ∧
    _ ≤ ENNReal.ofReal (2 * uniformRate α x ρ)
  unfold uniformRate
  by_cases ht : x < powerQuantileScale α ρ
  · simp only [ite_eq_left ht]
    have hT : 0 ≤ powerTail α x ρ := by
      rw [← power_tail_formula μ hα ha ha2 hρ hρ1 hm hx ht]
      apply integral_nonneg
      intro d
      exact le_min (by norm_num) (div_nonneg (mul_nonneg ha.le hx.le) d.2.1.le)
    obtain ⟨hl', hu'⟩ := clipped_sum_comparison hρ.le hT hl hu
    exact ⟨ENNReal.ofReal_le_ofReal hl', ENNReal.ofReal_le_ofReal hu'⟩
  · simp only [ite_eq_right ht]
    exact ⟨ENNReal.ofReal_le_ofReal (div_le_self hρ.le (Real.one_le_sqrt.2 (by norm_num))),
      ENNReal.ofReal_le_ofReal (by linarith)⟩

end ThresholdHC.PowerWindow
