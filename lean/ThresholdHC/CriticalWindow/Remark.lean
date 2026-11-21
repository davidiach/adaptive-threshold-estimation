import ThresholdHC.CriticalWindow.Measures
import ThresholdHC.CriticalEntropy.CriticalModel

/-! Remark 14.15 (v6 §14.8): reading the uniform rate.

* At `α = 2`, `a = 1/4` the window rate `Y` lies between twice and four times
  `√(ρ L H / B)`, the rate of the critical quadratic law, with `L H` the
  critical log factor (`quadratic_rate_bounds`), so the minimax risk of the
  quadratic law has explicit constants (`quadratic_risk_bounds`).
* Away from two, once `u = |1 - 2/α| log(1/ρ) ≥ 1`, `N_α(ρ) = 1/|α - 2|`,
  `Φ_α(ρ)` is within `1 - e^{-1}` of its leading term, and the risk is within
  universal factors of `min{ρ, x ρ^{min(1/2, 1-1/α)} √((1 + log(1/ε))/ε)}`.
* Near two, once `|α - 2| log(1/ρ) ≤ 1`, `Φ_α(ρ)` and `N_α(ρ)` are both of order
  `log(1/ρ)`. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.CriticalWindow
open ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Remark 14.15, first sentence: at `α = 2`, `a = 1/4` the window rate is the
rate `√(ρ L H / B)` of the critical quadratic law, within the factors 2 and 4. -/
theorem quadratic_rate_bounds {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    powerPhi 2 ρ = Real.log (1/ρ) ∧
    effectiveScales 2 ρ = 1 + Real.logb 2 (1/ρ) / 2 ∧
    2 * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B) ≤
      1 / ((1/4) * Real.sqrt B) *
        Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ∧
    1 / ((1/4) * Real.sqrt B) *
        Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ≤
      4 * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B) := by
  have hρ1 : ρ < 1 := by linarith
  have hphi : powerPhi 2 ρ = Real.log (1/ρ) := by
    have := power_phi_closed 2 ρ (by norm_num) hρ hρ1
    rwa [ite_eq_left (show (2 : ℝ) = 2 from rfl)] at this
  have hN : effectiveScales 2 ρ = 1 + Real.logb 2 (1/ρ) / 2 := by
    simp [effectiveScales]
  refine ⟨hphi, hN, ?_⟩
  set ℓ := Real.log (1/ρ) with hℓ
  have hℓ1 := log_inv_ge_one hρ hρ4
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog2 : 0 < Real.log 2 := by linarith
  set N := 1 + ℓ / (2 * Real.log 2) with hNdef
  have hNeq : effectiveScales 2 ρ = N := by
    rw [hN, hNdef, ← Real.log_div_log, hℓ]; ring
  have hN1 : 0 < N := by positivity
  have hNL : N ≤ 1 + ℓ := by
    rw [hNdef]
    have : ℓ / (2 * Real.log 2) ≤ ℓ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hNsq : 1 + ℓ ≤ N ^ 2 := by
    rw [hNdef]
    have h1 : ℓ ≤ 2 * (ℓ / (2 * Real.log 2)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]; nlinarith
    nlinarith [sq_nonneg (ℓ / (2 * Real.log 2)), div_nonneg (by linarith : (0:ℝ) ≤ ℓ)
      (by positivity : (0:ℝ) ≤ 2 * Real.log 2)]
  set L := 1 + ℓ with hL
  set H := 1 + Real.log L with hH
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hKup : 1 + Real.log N ≤ H := by
    have := Real.log_le_log hN1 hNL; linarith
  have hKlo : H / 2 ≤ 1 + Real.log N := by
    have h := Real.log_le_log (by linarith) hNsq
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hcrit : ThresholdHC.CriticalEntropy.criticalLogFactor ρ = L * H := by
    unfold ThresholdHC.CriticalEntropy.criticalLogFactor; rw [hH, hL, hℓ]
  rw [hcrit, hphi, hNeq]
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hK0 : 0 ≤ 1 + Real.log N := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hY : 1 / ((1/4) * Real.sqrt B) * Real.sqrt (ρ * ℓ * (1 + Real.log N)) =
      Real.sqrt (4^2 * (ρ * ℓ * (1 + Real.log N) / B)) := by
    rw [← mul_sqrt_eq (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_div (by positivity)]
    field_simp
  rw [hY, mul_sqrt_eq (by norm_num : (0:ℝ) ≤ 2), mul_sqrt_eq (by norm_num : (0:ℝ) ≤ 4)]
  have hℓL : L ≤ 2 * ℓ := by linarith
  constructor
  · apply Real.sqrt_le_sqrt
    rw [mul_div_assoc', mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hB.le
    have h1 : L * H ≤ (2 * ℓ) * (2 * (1 + Real.log N)) :=
      mul_le_mul hℓL (by linarith) (by linarith) (by linarith)
    nlinarith
  · apply Real.sqrt_le_sqrt
    rw [mul_div_assoc', mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hB.le
    have h1 : ℓ * (1 + Real.log N) ≤ L * H := mul_le_mul (by linarith) hKup hK0 (by linarith)
    nlinarith

/-- The consequence for the quadratic law `F(d) = (4d)^2`: its minimax risk lies
between `10^{-18}` and `1.36·10^6` times `min{ρ, √(ρ L H / B)}`. -/
theorem quadratic_risk_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ 2 (1/4)) :
    let C := Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ C) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (1360000 * min ρ C) := by
  intro C
  obtain ⟨-, -, hlo, hhi⟩ := quadratic_rate_bounds hρ hρ4 hB
  obtain ⟨hRl, hRu⟩ := risk_bounds μ (by norm_num : (3/2 : ℝ) ≤ 2) (by norm_num) (by norm_num)
    (by norm_num) hρ hρ4 hB hm
  set Y := 1 / ((1/4) * Real.sqrt B) *
    Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) with hY
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have h1 : min ρ C ≤ min ρ Y := min_le_min le_rfl (by linarith)
  have h2 : min ρ Y ≤ 4 * min ρ C := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
    exact min_le_min (by linarith) hhi
  have h0 : 0 ≤ min ρ C := le_min hρ.le hC0
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hRl
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine hRu.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith

/-- Remark 14.15, away from two: `N_α(ρ) = 1/|α - 2|` once `|1 - 2/α| log(1/ρ) ≥ 1`. -/
theorem away_scales_eq {α ρ : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (hα2 : α ≠ 2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hu : 1 ≤ |1 - 2/α| * Real.log (1/ρ)) :
    effectiveScales α ρ = 1 / |α - 2| := by
  have hα : 0 < α := by linarith
  have hε : 0 < |α - 2| := abs_pos.2 (sub_ne_zero.2 hα2)
  have hε1 : |α - 2| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hℓ1 := log_inv_ge_one hρ hρ4
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  unfold effectiveScales
  rw [ite_eq_right hα2]
  have hmax : max 1 (1 / |α - 2|) = 1 / |α - 2| :=
    max_eq_right (by rw [le_div_iff₀ hε]; linarith)
  rw [hmax]
  apply min_eq_right
  rw [abs_one_sub_two_div hα] at hu
  have h1 : 1 / |α - 2| ≤ Real.log (1/ρ) / α := by
    rw [div_le_div_iff₀ hε hα]
    have : 1 ≤ |α - 2| * Real.log (1/ρ) / α := by
      calc (1 : ℝ) ≤ |α - 2| / α * Real.log (1/ρ) := hu
        _ = |α - 2| * Real.log (1/ρ) / α := by ring
    rw [le_div_iff₀ hα] at this
    linarith
  have h2 : Real.log (1/ρ) / α ≤ Real.logb 2 (1/ρ) / α := by
    apply div_le_div_of_nonneg_right _ hα.le
    rw [← Real.log_div_log, le_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Remark 14.15, away from two: `Φ_α(ρ)` lies between `1 - e^{-1}` and `1` times
`α/(α - 2)` above two, and times `α ρ^{1-2/α}/(2 - α)` below two. -/
theorem away_phi_bounds {α ρ : ℝ} (hα1 : 3/2 ≤ α)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hu : 1 ≤ |1 - 2/α| * Real.log (1/ρ)) :
    (2 < α → (1 - Real.exp (-1)) * (α / (α - 2)) ≤ powerPhi α ρ ∧
      powerPhi α ρ ≤ α / (α - 2)) ∧
    (α < 2 → (1 - Real.exp (-1)) * (α * ρ ^ (1 - 2/α) / (2 - α)) ≤ powerPhi α ρ ∧
      powerPhi α ρ ≤ α * ρ ^ (1 - 2/α) / (2 - α)) := by
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hclosed := power_phi_closed α ρ hα hρ hρ1
  constructor
  · intro h2
    rw [ite_eq_right (by linarith : α ≠ 2)] at hclosed
    rw [hclosed]
    have hc : 0 < 1 - 2/α := by rw [sub_pos, div_lt_one hα]; linarith
    rw [abs_of_pos hc] at hu
    have hpow : ρ ^ (1 - 2/α) ≤ Real.exp (-1) := by
      rw [rpow_exp_form hρ]; exact Real.exp_le_exp.2 (by linarith)
    have hpow0 : 0 ≤ ρ ^ (1 - 2/α) := Real.rpow_nonneg hρ.le _
    have hd : 0 < α - 2 := by linarith
    constructor
    · rw [mul_div_assoc', div_le_div_iff_of_pos_right hd]
      nlinarith
    · rw [div_le_div_iff_of_pos_right hd]; nlinarith
  · intro h2
    rw [ite_eq_right (by linarith : α ≠ 2)] at hclosed
    rw [hclosed]
    have hc : 1 - 2/α < 0 := by rw [sub_neg, lt_div_iff₀ hα]; linarith
    rw [abs_of_neg hc] at hu
    set t := ρ ^ (2/α - 1) with ht
    have htexp : t ≤ Real.exp (-1) := by
      rw [ht, rpow_exp_form hρ]; exact Real.exp_le_exp.2 (by linarith)
    have hprod : ρ ^ (1 - 2/α) * t = 1 := by
      rw [ht, ← Real.rpow_add hρ, show 1 - 2/α + (2/α - 1) = 0 by ring, Real.rpow_zero]
    have hP0 : 0 < ρ ^ (1 - 2/α) := Real.rpow_pos_of_pos hρ _
    have hd : 0 < 2 - α := by linarith
    have hform : α * (1 - ρ ^ (1 - 2/α)) / (α - 2) = α * (ρ ^ (1 - 2/α) - 1) / (2 - α) := by
      rw [show α - 2 = -(2 - α) by ring, div_neg, ← neg_div]; ring_nf
    rw [hform]
    have hid : ρ ^ (1 - 2/α) - 1 = ρ ^ (1 - 2/α) * (1 - t) := by
      rw [mul_sub, mul_one, hprod]
    have hαP : 0 ≤ α * ρ ^ (1 - 2/α) := by positivity
    constructor
    · rw [mul_div_assoc', div_le_div_iff_of_pos_right hd, hid]
      nlinarith [mul_le_mul_of_nonneg_left (show 1 - Real.exp (-1) ≤ 1 - t by linarith) hαP]
    · rw [div_le_div_iff_of_pos_right hd]
      nlinarith

/-- In the regime away from two, the window rate `Y` is within the factor 2 of
`Z = x ρ^{min(1/2, 1-1/α)} √((1 + log(1/ε))/ε)`. -/
theorem away_rate_bounds {α ρ x : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (hα2 : α ≠ 2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : 0 < x) (hu : 1 ≤ |1 - 2/α| * Real.log (1/ρ)) :
    x * ρ ^ (min (1/2) (1 - 1/α)) * Real.sqrt ((1 + Real.log (1 / |α - 2|)) / |α - 2|) / 2 ≤
      x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ∧
    x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤
      2 * (x * ρ ^ (min (1/2) (1 - 1/α)) * Real.sqrt ((1 + Real.log (1 / |α - 2|)) / |α - 2|)) := by
  have hα : 0 < α := by linarith
  have hε : 0 < |α - 2| := abs_pos.2 (sub_ne_zero.2 hα2)
  have hε1 : |α - 2| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  rw [away_scales_eq hα1 hα3 hα2 hρ hρ4 hu]
  set ε := |α - 2| with hεdef
  set K := 1 + Real.log (1 / ε) with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ Real.log (1/ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    linarith
  set m := min (1/2 : ℝ) (1 - 1/α) with hm
  -- `ρ^m √(K/ε) = √(ρ^{2m} K/ε)`
  have hρm : ρ ^ m * Real.sqrt (K / ε) = Real.sqrt (ρ ^ (2*m) * (K / ε)) := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hρ.le _), show 2*m = m*2 by ring,
      Real.rpow_mul hρ.le, show ((ρ ^ m) ^ (2:ℝ)) = (ρ ^ m)^2 by norm_cast,
      Real.sqrt_sq (Real.rpow_nonneg hρ.le _)]
  -- the two-sided bound on `ρ Φ K` against `ρ^{2m} K / ε`
  have hphi := away_phi_bounds hα1 hρ hρ4 hu
  have hcmp : ρ ^ (2*m) * (K / ε) / 4 ≤ ρ * powerPhi α ρ * K ∧
      ρ * powerPhi α ρ * K ≤ 4 * (ρ ^ (2*m) * (K / ε)) := by
    have he1 : Real.exp (-1) ≤ 37/100 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    have hK0 : 0 ≤ K := by linarith
    rcases lt_or_gt_of_ne hα2 with h2 | h2
    · obtain ⟨hl, hu'⟩ := hphi.2 h2
      have hεv : ε = 2 - α := by rw [hεdef, abs_of_neg (by linarith)]; ring
      have hmv : m = 1 - 1/α := by
        rw [hm]; apply min_eq_right
        have : 1/α ≥ 1/2 := by rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hα]; linarith
        linarith
      have h2m : ρ ^ (2*m) = ρ * ρ ^ (1 - 2/α) := by
        rw [hmv, show 2 * (1 - 1/α) = 1 + (1 - 2/α) by ring, Real.rpow_add hρ, Real.rpow_one]
      rw [h2m, hεv]
      have hP := Real.rpow_pos_of_pos hρ (1 - 2/α)
      have hd : 0 < 2 - α := by linarith
      have e1 : ρ * (α * ρ ^ (1 - 2/α) / (2 - α)) * K = α * (ρ * ρ ^ (1 - 2/α) * (K / (2 - α))) := by
        field_simp
      constructor
      · have : (1 - Real.exp (-1)) * α ≥ 1/4 := by nlinarith
        calc ρ * ρ ^ (1 - 2/α) * (K / (2 - α)) / 4
            ≤ (1 - Real.exp (-1)) * α * (ρ * ρ ^ (1 - 2/α) * (K / (2 - α))) := by
              have hq : 0 ≤ ρ * ρ ^ (1 - 2/α) * (K / (2 - α)) := by positivity
              nlinarith
          _ = ρ * ((1 - Real.exp (-1)) * (α * ρ ^ (1 - 2/α) / (2 - α))) * K := by
              field_simp
          _ ≤ ρ * powerPhi α ρ * K := by
              apply mul_le_mul_of_nonneg_right _ hK0
              exact mul_le_mul_of_nonneg_left hl hρ.le
      · calc ρ * powerPhi α ρ * K ≤ ρ * (α * ρ ^ (1 - 2/α) / (2 - α)) * K := by
              apply mul_le_mul_of_nonneg_right _ hK0
              exact mul_le_mul_of_nonneg_left hu' hρ.le
          _ = α * (ρ * ρ ^ (1 - 2/α) * (K / (2 - α))) := e1
          _ ≤ 4 * (ρ * ρ ^ (1 - 2/α) * (K / (2 - α))) := by
              have hq : 0 ≤ ρ * ρ ^ (1 - 2/α) * (K / (2 - α)) := by positivity
              nlinarith
    · obtain ⟨hl, hu'⟩ := hphi.1 h2
      have hεv : ε = α - 2 := by rw [hεdef, abs_of_pos (by linarith)]
      have hmv : m = 1/2 := by
        rw [hm]; apply min_eq_left
        have : 1/α ≤ 1/2 := by rw [div_le_div_iff₀ hα (by norm_num)]; linarith
        linarith
      have h2m : ρ ^ (2*m) = ρ := by rw [hmv]; norm_num
      rw [h2m, hεv]
      have hd : 0 < α - 2 := by linarith
      constructor
      · have : (1 - Real.exp (-1)) * α ≥ 1/4 := by nlinarith
        calc ρ * (K / (α - 2)) / 4 ≤ (1 - Real.exp (-1)) * α * (ρ * (K / (α - 2))) := by
              have hq : 0 ≤ ρ * (K / (α - 2)) := by positivity
              nlinarith
          _ = ρ * ((1 - Real.exp (-1)) * (α / (α - 2))) * K := by field_simp
          _ ≤ ρ * powerPhi α ρ * K := by
              apply mul_le_mul_of_nonneg_right _ hK0
              exact mul_le_mul_of_nonneg_left hl hρ.le
      · calc ρ * powerPhi α ρ * K ≤ ρ * (α / (α - 2)) * K := by
              apply mul_le_mul_of_nonneg_right _ hK0
              exact mul_le_mul_of_nonneg_left hu' hρ.le
          _ = α * (ρ * (K / (α - 2))) := by field_simp
          _ ≤ 4 * (ρ * (K / (α - 2))) := by
              have hq : 0 ≤ ρ * (K / (α - 2)) := by positivity
              nlinarith
  obtain ⟨hlo, hhi⟩ := hcmp
  rw [mul_assoc x, hρm]
  have hQ0 : 0 ≤ ρ ^ (2*m) * (K / ε) := by positivity
  constructor
  · have h := Real.sqrt_le_sqrt hlo
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h hx.le
  · have h := Real.sqrt_le_sqrt hhi
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    nlinarith [mul_le_mul_of_nonneg_left h hx.le]

open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Remark 14.15, away from two: the minimax risk is within universal factors of
`min{ρ, x ρ^{min(1/2, 1-1/α)} √((1 + log(1/ε))/ε)}`. -/
theorem away_risk_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (hα2 : α ≠ 2) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a)
    (hu : 1 ≤ |1 - 2/α| * Real.log (1/ρ)) :
    let Z := 1 / (a * Real.sqrt B) * ρ ^ (min (1/2) (1 - 1/α)) *
      Real.sqrt ((1 + Real.log (1 / |α - 2|)) / |α - 2|)
    ENNReal.ofReal (5 * (10 : ℝ)⁻¹ ^ 19 * min ρ Z) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (700000 * min ρ Z) := by
  intro Z
  have hx : 0 < 1 / (a * Real.sqrt B) := by positivity
  obtain ⟨hlo, hhi⟩ := away_rate_bounds hα1 hα3 hα2 hρ hρ4 hx hu
  obtain ⟨hRl, hRu⟩ := risk_bounds μ hα1 hα3 ha ha2 hρ hρ4 hB hm
  set Y := 1 / (a * Real.sqrt B) *
    Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) with hY
  have hZ0 : 0 ≤ Z := by positivity
  have hm1 : min ρ Z / 2 ≤ min ρ Y := by
    rw [le_min_iff]; constructor
    · linarith [min_le_left ρ Z, hρ]
    · linarith [min_le_right ρ Z]
  have hm2 : min ρ Y ≤ 2 * min ρ Z := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    exact min_le_min (by linarith) hhi
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hRl
    have h0 : 0 ≤ min ρ Z := le_min hρ.le hZ0
    have hc : 5 * (10 : ℝ)⁻¹ ^ 19 * 2 = (10 : ℝ)⁻¹ ^ 18 := by norm_num
    nlinarith [pow_pos (show (0 : ℝ) < 10⁻¹ by norm_num) 18]
  · refine hRu.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith

/-- Remark 14.15, near two: once `ε log(1/ρ) ≤ 1`, both `Φ_α(ρ)` and `N_α(ρ)` are of
order `log(1/ρ)`, as for the quadratic law. -/
theorem near_two_bounds {α ρ : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hε : |α - 2| * Real.log (1/ρ) ≤ 1) :
    Real.log (1/ρ) / 2 ≤ powerPhi α ρ ∧ powerPhi α ρ ≤ 2 * Real.log (1/ρ) ∧
    Real.log (1/ρ) / 3 ≤ effectiveScales α ρ ∧ effectiveScales α ρ ≤ 2 * Real.log (1/ρ) := by
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  set ℓ := Real.log (1/ρ) with hℓ
  have hℓ1 : 1 ≤ ℓ := log_inv_ge_one hρ hρ4
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hclosed := power_phi_closed α ρ hα hρ hρ1
  -- Φ
  have hphi : ℓ / 2 ≤ powerPhi α ρ ∧ powerPhi α ρ ≤ 2 * ℓ := by
    rcases lt_trichotomy α 2 with h2 | h2 | h2
    · rw [ite_eq_right (by linarith : α ≠ 2)] at hclosed
      rw [hclosed]
      set u := (2/α - 1) * ℓ with hu
      have hu0 : 0 ≤ u := by
        rw [hu]; apply mul_nonneg _ (by linarith)
        rw [sub_nonneg, le_div_iff₀ hα]; linarith
      have hε' : |α - 2| = 2 - α := by rw [abs_of_neg (by linarith)]; ring
      have hu1 : u ≤ 1 := by
        rw [hu, show 2/α - 1 = (2 - α)/α by field_simp]
        rw [hε'] at hε
        rw [div_mul_eq_mul_div, div_le_one hα]
        linarith
      have hP : ρ ^ (1 - 2/α) = Real.exp u := by
        rw [rpow_exp_form hρ, hu]; congr 1; ring
      rw [hP]
      have hd : 0 < 2 - α := by linarith
      have hform : α * (1 - Real.exp u) / (α - 2) = α * (Real.exp u - 1) / (2 - α) := by
        rw [show α - 2 = -(2 - α) by ring, div_neg, ← neg_div]; ring_nf
      rw [hform]
      have hαu : α * u = (2 - α) * ℓ := by rw [hu]; field_simp
      have hlo := Real.add_one_le_exp u
      have hhi : Real.exp u - 1 ≤ 2 * u := by
        have := Real.abs_exp_sub_one_le (show |u| ≤ 1 by rw [abs_of_nonneg hu0]; exact hu1)
        rw [abs_of_nonneg hu0] at this
        exact (le_abs_self _).trans this
      constructor
      · rw [le_div_iff₀ hd]; nlinarith
      · rw [div_le_iff₀ hd]; nlinarith
    · subst h2
      rw [ite_eq_left rfl] at hclosed
      rw [hclosed]; constructor <;> linarith
    · rw [ite_eq_right (by linarith : α ≠ 2)] at hclosed
      rw [hclosed]
      set u := (1 - 2/α) * ℓ with hu
      have hu0 : 0 ≤ u := by
        rw [hu]; apply mul_nonneg _ (by linarith)
        rw [sub_nonneg, div_le_one hα]; linarith
      have hε' : |α - 2| = α - 2 := abs_of_pos (by linarith)
      have hu23 : u ≤ 2/3 := by
        rw [hu, show 1 - 2/α = (α - 2)/α by field_simp]
        rw [hε'] at hε
        rw [div_mul_eq_mul_div, div_le_iff₀ hα]
        linarith
      have hP : ρ ^ (1 - 2/α) = Real.exp (-u) := by
        rw [rpow_exp_form hρ, hu]
      rw [hP]
      have hd : 0 < α - 2 := by linarith
      have hαu : α * u = (α - 2) * ℓ := by rw [hu]; field_simp
      have h1 : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
      have hexp : Real.exp u ≤ 2 := (Real.exp_le_exp.2 hu23).trans exp_two_thirds_le
      have hprod : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
      have h2' : u / 2 ≤ 1 - Real.exp (-u) := by
        have he := Real.add_one_le_exp u
        have hpos := Real.exp_pos (-u)
        nlinarith
      constructor
      · rw [le_div_iff₀ hd]; nlinarith
      · rw [div_le_iff₀ hd]; nlinarith
  refine ⟨hphi.1, hphi.2, ?_⟩
  -- N
  have hlb : ℓ / (α * Real.log 2) = Real.logb 2 (1/ρ) / α := by
    rw [← Real.log_div_log, hℓ]; field_simp
  unfold effectiveScales
  split_ifs with h2
  · subst h2
    have hb : Real.logb 2 (1/ρ) / 2 = ℓ / (2 * Real.log 2) := by rw [← hlb]
    rw [hb]
    constructor
    · have : ℓ / 3 ≤ ℓ / (2 * Real.log 2) := by
        apply div_le_div_of_nonneg_left (by linarith) (by positivity); linarith
      linarith
    · have : ℓ / (2 * Real.log 2) ≤ ℓ := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
  · have hε0 : 0 < |α - 2| := abs_pos.2 (sub_ne_zero.2 h2)
    rw [← hlb]
    constructor
    · apply le_min
      · have : ℓ / 3 ≤ ℓ / (α * Real.log 2) := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity); nlinarith
        have : 0 ≤ ℓ / (α * Real.log 2) := by positivity
        linarith
      · have : ℓ ≤ 1 / |α - 2| := by rw [le_div_iff₀ hε0]; linarith
        have := le_max_right 1 (1 / |α - 2|)
        linarith
    · refine (min_le_left _ _).trans ?_
      have h1 : 1 ≤ α * Real.log 2 := by nlinarith
      have : ℓ / (α * Real.log 2) ≤ ℓ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ ℓ)]
      linarith

/-- Remark 14.15 at exponent two: `Φ_2(ρ)` and `N_2(ρ)` are each within universal
factors of `L = 1 + log(1/ρ)`; precisely `L/2 ≤ Φ_2(ρ) ≤ L` and `N_2(ρ) ≤ L ≤ N_2(ρ)^2`. -/
theorem quadratic_scales_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    (1 + Real.log (1/ρ)) / 2 ≤ powerPhi 2 ρ ∧ powerPhi 2 ρ ≤ 1 + Real.log (1/ρ) ∧
    effectiveScales 2 ρ ≤ 1 + Real.log (1/ρ) ∧ 1 + Real.log (1/ρ) ≤ effectiveScales 2 ρ ^ 2 := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hℓ1 := log_inv_ge_one hρ hρ4
  have hphi : powerPhi 2 ρ = Real.log (1/ρ) := by
    have := power_phi_closed 2 ρ (by norm_num) hρ (by linarith)
    rwa [ite_eq_left (show (2 : ℝ) = 2 from rfl)] at this
  set ℓ := Real.log (1/ρ) with hℓ
  have hN : effectiveScales 2 ρ = 1 + ℓ / (2 * Real.log 2) := by
    simp only [effectiveScales, ite_true]
    rw [← Real.log_div_log, hℓ]; ring
  rw [hphi, hN]
  have hq : 0 ≤ ℓ / (2 * Real.log 2) := by positivity
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have : ℓ / (2 * Real.log 2) ≤ ℓ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · have h1 : ℓ ≤ 2 * (ℓ / (2 * Real.log 2)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]; nlinarith
    nlinarith [sq_nonneg (ℓ / (2 * Real.log 2))]

/-- Remark 14.15, near two, for the risk: once `|α - 2| log(1/ρ) ≤ 1`, the minimax risk
is within universal factors of `min{ρ, x √(ρ L H)}`, the rate of the quadratic law. -/
theorem near_two_risk_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B : ℝ} (hα1 : 3/2 ≤ α) (hα3 : α ≤ 3) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a)
    (hε : |α - 2| * Real.log (1/ρ) ≤ 1) :
    let Z := 1 / (a * Real.sqrt B) *
      Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ)
    ENNReal.ofReal (2 * (10 : ℝ)⁻¹ ^ 19 * min ρ Z) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (700000 * min ρ Z) := by
  intro Z
  have hα : 0 < α := by linarith
  have hρ1 : ρ < 1 := by linarith
  obtain ⟨hΦl, hΦu, hNl, hNu⟩ := near_two_bounds hα1 hα3 hρ hρ4 hε
  have hN1 := effective_scales_ge_one hα hρ hρ1
  set ℓ := Real.log (1/ρ) with hℓ
  have hℓ1 : 1 ≤ ℓ := log_inv_ge_one hρ hρ4
  set L := 1 + ℓ with hL
  set H := 1 + Real.log L with hH
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hcrit : ThresholdHC.CriticalEntropy.criticalLogFactor ρ = L * H := by
    unfold ThresholdHC.CriticalEntropy.criticalLogFactor; rw [hH, hL, hℓ]
  set N := effectiveScales α ρ with hNdef
  set K := 1 + Real.log N with hKdef
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  -- K ≤ 2 H
  have hKup : K ≤ 2 * H := by
    have h1 : Real.log N ≤ Real.log (2 * L) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have := Real.log_two_lt_d9
    linarith
  -- K ≥ H/3
  have hKlo : H / 3 ≤ K := by
    have h6 : Real.log 6 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have he := Real.exp_one_gt_d9
      nlinarith
    have h1 : Real.log (L / 6) ≤ Real.log N := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    by_cases hH3 : H ≤ 3
    · linarith
    · linarith
  -- the radicands
  have hP : ρ * (L * H) / 16 ≤ ρ * powerPhi α ρ * K ∧ ρ * powerPhi α ρ * K ≤ 4 * (ρ * (L * H)) := by
    have hΦL : L / 4 ≤ powerPhi α ρ := by linarith
    have hΦU : powerPhi α ρ ≤ 2 * L := by linarith
    have hH1 : 1 ≤ H := by linarith
    have hK0 : 0 ≤ K := by linarith
    constructor
    · have : L * H / 16 ≤ powerPhi α ρ * K := by
        have := mul_le_mul hΦL hKlo (by positivity) (by linarith)
        nlinarith
      nlinarith
    · have : powerPhi α ρ * K ≤ 4 * (L * H) := by
        have := mul_le_mul hΦU hKup hK0 (by linarith)
        nlinarith
      nlinarith
  obtain ⟨hRl, hRu⟩ := risk_bounds μ hα1 hα3 ha ha2 hρ hρ4 hB hm
  set x := 1 / (a * Real.sqrt B) with hx
  have hx0 : 0 < x := by positivity
  set Y := x * Real.sqrt (ρ * powerPhi α ρ * K) with hY
  have hZ : Z = x * Real.sqrt (ρ * (L * H)) := by rw [← hcrit]
  have hYlo : Z / 4 ≤ Y := by
    rw [hZ, hY]
    have h := Real.sqrt_le_sqrt hP.1
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 16),
      show Real.sqrt 16 = 4 by rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h hx0.le
  have hYhi : Y ≤ 2 * Z := by
    rw [hZ, hY]
    have h := Real.sqrt_le_sqrt hP.2
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    nlinarith [mul_le_mul_of_nonneg_left h hx0.le]
  have hZ0 : 0 ≤ Z := by positivity
  have hm1 : min ρ Z / 4 ≤ min ρ Y := by
    rw [le_min_iff]; constructor
    · linarith [min_le_left ρ Z]
    · linarith [min_le_right ρ Z]
  have hm2 : min ρ Y ≤ 2 * min ρ Z := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    exact min_le_min (by linarith) hYhi
  have h0 : 0 ≤ min ρ Z := le_min hρ.le hZ0
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hRl
    have hc : 2 * (10 : ℝ)⁻¹ ^ 19 * 4 ≤ (10 : ℝ)⁻¹ ^ 18 := by norm_num
    nlinarith [pow_pos (show (0 : ℝ) < 10⁻¹ by norm_num) 18]
  · refine hRu.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith

end ThresholdHC.CriticalWindow
