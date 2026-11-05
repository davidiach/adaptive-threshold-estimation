import Mathlib

noncomputable section
namespace ThresholdHC.SmoothDensity

def scaleConstant (s : ℕ) : ℝ := 64 * (s + 1 : ℕ)

def radiusCutoff (s : ℕ) : ℝ :=
  min (Real.exp (-(2 * Real.log (scaleConstant s) + 2)))
    ((1 / 64 : ℝ) ^ (s + 1) / scaleConstant s)

theorem scaleConstant_pos (s : ℕ) : 0 < scaleConstant s := by
  unfold scaleConstant
  positivity

theorem radiusCutoff_pos (s : ℕ) : 0 < radiusCutoff s := by
  unfold radiusCutoff
  exact lt_min (Real.exp_pos _) (div_pos (by positivity) (scaleConstant_pos s))

/-- A scale chosen from the requested accuracy has logarithmic separation. -/
theorem choose_smooth_scale (s : ℕ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ radiusCutoff s) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 64 ∧
      t ^ (s + 1) = scaleConstant s * ε / Real.log (1 / ε) ∧
      2 * ε < t ^ (s + 1) / 8 * Real.log (1 / t) := by
  let K := scaleConstant s
  let L := Real.log (1 / ε)
  have hK : 0 < K := scaleConstant_pos s
  have hK1 : 1 ≤ K := by
    dsimp [K,scaleConstant]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have hn : (0 : ℝ) < (s + 1 : ℕ) := by positivity
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have he₁ : ε ≤ Real.exp (-(2 * Real.log K + 2)) := hsmall.trans (min_le_left _ _)
  have he₂ : ε ≤ (1 / 64 : ℝ) ^ (s + 1) / K := hsmall.trans (min_le_right _ _)
  have hL : 2 * Real.log K + 2 ≤ L := by
    have h := Real.log_le_log hε he₁
    rw [Real.log_exp] at h
    dsimp [L]
    rw [Real.log_div one_ne_zero (ne_of_gt hε), Real.log_one]
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  let h := K * ε / L
  have hh : 0 < h := div_pos (mul_pos hK hε) hL0
  have hcap : h ≤ (1 / 64 : ℝ) ^ (s + 1) := by
    have hdiv : h ≤ K * ε := div_le_self (mul_nonneg hK.le hε.le) hL1
    exact hdiv.trans (by nlinarith [(le_div_iff₀ hK).mp he₂])
  let t := h ^ (((s + 1 : ℕ) : ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos hh _
  have htcap : t ≤ 1 / 64 := by
    have hb := Real.rpow_le_rpow hh.le hcap (inv_nonneg.mpr hn.le)
    simpa only [Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (by omega : s + 1 ≠ 0)] using hb
  have hpow : t ^ (s + 1) = h := Real.rpow_inv_natCast_pow hh.le (by omega)
  have hhlog : L / 2 ≤ Real.log (1 / h) := by
    dsimp [h]
    rw [Real.log_div one_ne_zero hh.ne', Real.log_one,
      Real.log_div (mul_ne_zero hK.ne' hε.ne') hL0.ne',
      Real.log_mul hK.ne' hε.ne']
    have hle : 0 ≤ Real.log L := Real.log_nonneg hL1
    have he : Real.log ε = -L := by
      dsimp [L]
      rw [Real.log_div one_ne_zero hε.ne', Real.log_one]
      ring
    rw [he]
    linarith
  have hlogpow : (s + 1 : ℕ) * Real.log (1 / t) = Real.log (1 / h) := by
    rw [← Real.log_pow, one_div_pow, hpow]
  refine ⟨t,ht,htcap,hpow,?_⟩
  have hprod := mul_le_mul_of_nonneg_left hhlog (show 0 ≤ h / (8 * (s + 1 : ℕ)) by positivity)
  have hleft : h / (8 * (s + 1 : ℕ)) * (L / 2) = 4 * ε := by
    dsimp [h,K,scaleConstant]
    field_simp
    ring
  have hright : h / (8 * (s + 1 : ℕ)) * Real.log (1 / h) =
      t ^ (s + 1) / 8 * Real.log (1 / t) := by
    rw [← hlogpow,hpow]
    field_simp
  rw [hleft,hright] at hprod
  linarith

end ThresholdHC.SmoothDensity
