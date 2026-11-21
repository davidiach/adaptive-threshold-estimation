import ThresholdHC.PaperCorollaries.Specification
import ThresholdHC.CriticalWindow.Full

/-! The paper's divergence sequence for `Ψ` at the quadratic law.

At `α = 2`, `a = 1/4`, `ρ = exp(-ℓ)` and `B = ρ^{-2}` the window rate is
`Y = 4ρ √(ρ ℓ K)` with `K = 1 + log N_2(ρ)`, and `Y ≤ ρ` once `ℓ ≥ 20`, because
`16 ℓ (1 + ℓ) ≤ ℓ^5/120 ≤ e^ℓ`. The ratio statement of Corollary 14.14 then
bounds the risk below by `10^{-19} √K Ψ`, and `K ≥ (1 + log(1 + ℓ))/2` since
`N_2(ρ)^2 ≥ 1 + ℓ`. With `ℓ = e^n` and `n ≥ 3`, `ℓ ≥ 20`. -/
noncomputable section
open MeasureTheory
namespace ThresholdHC.PaperCorollaries
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow ThresholdHC.CriticalWindow

/-- `16 ℓ (1 + ℓ) ≤ e^ℓ` for `ℓ ≥ 20`. -/
theorem sixteen_le_exp {ℓ : ℝ} (hℓ : 20 ≤ ℓ) : 16 * ℓ * (1 + ℓ) ≤ Real.exp ℓ := by
  have h5 := Real.pow_div_factorial_le_exp (x := ℓ) (by linarith) 5
  have hf : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at h5
  have hℓ0 : 0 ≤ ℓ := by linarith
  have h3 : (8000 : ℝ) ≤ ℓ ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hℓ 3]
  have : 1920 * (ℓ * (1 + ℓ)) ≤ ℓ ^ 5 := by nlinarith [mul_nonneg hℓ0 hℓ0]
  nlinarith

theorem exp_three_ge : (20 : ℝ) ≤ Real.exp 3 := by
  have he := Real.exp_one_gt_d9
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 3]

theorem psi_sequence_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hm : ExactPowerLaw μ 2 (1/4)) (n : ℕ) (hn : 3 ≤ n) :
    ENNReal.ofReal (7 * (10 : ℝ)⁻¹ ^ 20 *
        Real.sqrt (1 + Real.log (1 + Real.log (1 / Real.exp (-Real.exp n))))) *
        rarePsi μ (Real.exp (-Real.exp n)) (1 / Real.sqrt (1 / Real.exp (-Real.exp n) ^ 2)) ≤
      rareMinimaxRisk μ (Real.exp (-Real.exp n)) (1 / Real.exp (-Real.exp n) ^ 2) ∧
    Real.sqrt (1 + n) ≤ Real.sqrt (1 + Real.log (1 + Real.log (1 / Real.exp (-Real.exp n)))) := by
  set ℓ := Real.exp (n : ℝ) with hℓdef
  set ρ := Real.exp (-ℓ) with hρdef
  have hρ : 0 < ρ := Real.exp_pos _
  have hlog : Real.log (1/ρ) = ℓ := by rw [hρdef, one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hℓ20 : 20 ≤ ℓ := by
    rw [hℓdef]
    exact exp_three_ge.trans (Real.exp_le_exp.2 (by exact_mod_cast hn))
  have hρ4 : ρ ≤ 1/4 := by
    have h1 : ρ ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-2) ≤ 1/4 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.add_one_le_exp 2
      have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have he := Real.exp_one_gt_d9
      nlinarith
    linarith
  set B := 1 / ρ ^ 2 with hBdef
  have hB : 0 < B := by positivity
  have hsB : Real.sqrt B = 1 / ρ := by
    rw [hBdef, Real.sqrt_div' _ (sq_nonneg ρ), Real.sqrt_one, Real.sqrt_sq hρ.le]
  obtain ⟨-, -, hNup, hNsq⟩ := quadratic_scales_bounds hρ hρ4
  rw [hlog] at hNsq hNup
  have hN1 : 1 ≤ effectiveScales 2 ρ := effective_scales_ge_one (by norm_num) hρ (by linarith)
  set K := 1 + Real.log (effectiveScales 2 ρ) with hKdef
  have hK0 : 0 ≤ K := by linarith [Real.log_nonneg hN1]
  have hKup : K ≤ 1 + ℓ := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < effectiveScales 2 ρ)
    linarith
  have hphi : powerPhi 2 ρ = ℓ := by
    rw [← hlog]; exact (window_quadratic_rate ρ B hρ hρ4 hB).1
  -- Y ≤ ρ
  have hY : 1 / ((1/4) * Real.sqrt B) * Real.sqrt (ρ * powerPhi 2 ρ * K) ≤ ρ := by
    rw [hsB, hphi]
    have hpre : 1 / ((1/4) * (1 / ρ)) = 4 * ρ := by field_simp
    rw [hpre]
    have hsmall : ρ * ℓ * K ≤ (1/4)^2 := by
      have he := sixteen_le_exp hℓ20
      have hρe : ρ * Real.exp ℓ = 1 := by rw [hρdef, ← Real.exp_add]; simp
      have h1 : ρ * ℓ * K ≤ ρ * ℓ * (1 + ℓ) :=
        mul_le_mul_of_nonneg_left hKup (by positivity)
      have h2 : 16 * (ρ * ℓ * (1 + ℓ)) ≤ ρ * Real.exp ℓ := by
        have := mul_le_mul_of_nonneg_left he hρ.le; nlinarith
      nlinarith
    have hs : Real.sqrt (ρ * ℓ * K) ≤ 1/4 := by
      rw [show (1/4 : ℝ) = Real.sqrt ((1/4)^2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hsmall
    nlinarith [Real.sqrt_nonneg (ρ * ℓ * K)]
  obtain ⟨hlo, -⟩ := critical_window_ratio μ 2 (1/4) ρ B (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hρ hρ4 hB hm hY
  -- K ≥ (1 + log(1 + ℓ))/2
  have hKlo : (1 + Real.log (1 + ℓ)) / 2 ≤ K := by
    have h := Real.log_le_log (by linarith) hNsq
    rw [Real.log_pow] at h
    push_cast at h
    have : 0 ≤ Real.log (1 + ℓ) := Real.log_nonneg (by linarith)
    linarith
  have hs2 := ThresholdHC.CriticalWindow.sqrt_two_le
  have hH0 : 0 ≤ 1 + Real.log (1 + ℓ) := by
    have : 0 ≤ Real.log (1 + ℓ) := Real.log_nonneg (by linarith)
    linarith
  have hroot : 7 * (10 : ℝ)⁻¹ ^ 20 * Real.sqrt (1 + Real.log (1 + ℓ)) ≤
      (10 : ℝ)⁻¹ ^ 19 * Real.sqrt K := by
    have hsq : Real.sqrt (1 + Real.log (1 + ℓ)) ≤ Real.sqrt 2 * Real.sqrt K := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    have hc : 7 * (10 : ℝ)⁻¹ ^ 20 * Real.sqrt 2 ≤ (10 : ℝ)⁻¹ ^ 19 := by
      have : (10 : ℝ)⁻¹ ^ 19 = 10 * (10 : ℝ)⁻¹ ^ 20 := by norm_num
      rw [this]; nlinarith [pow_pos (show (0:ℝ) < 10⁻¹ by norm_num) 20]
    calc 7 * (10 : ℝ)⁻¹ ^ 20 * Real.sqrt (1 + Real.log (1 + ℓ))
        ≤ 7 * (10 : ℝ)⁻¹ ^ 20 * (Real.sqrt 2 * Real.sqrt K) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 7 * (10 : ℝ)⁻¹ ^ 20 * Real.sqrt 2 * Real.sqrt K := by ring
      _ ≤ (10 : ℝ)⁻¹ ^ 19 * Real.sqrt K := mul_le_mul_of_nonneg_right hc hsK
  rw [hlog]
  constructor
  · refine le_trans ?_ hlo
    gcongr
  · apply Real.sqrt_le_sqrt
    have h1 : (n : ℝ) ≤ Real.log (1 + ℓ) := by
      rw [show (n : ℝ) = Real.log ℓ by rw [hℓdef, Real.log_exp]]
      exact Real.log_le_log (by positivity) (by linarith)
    linarith

end ThresholdHC.PaperCorollaries
