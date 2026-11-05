import ThresholdHC.ContinuousObserved.UniformGaps
import ThresholdHC.SmoothDensity.Scale

noncomputable section
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.SmoothDensity

theorem choose_observed_scale {ε : ℝ} (hε : 0 < ε) (he : ε ≤ radiusCutoff 0) :
    ∃ h : Gap, (h : ℝ) ≤ 1 / 64 ∧
      (h : ℝ) = 64 * ε / Real.log (1 / ε) ∧
      ε < modulus uniformGaps h / 32 := by
  obtain ⟨t,ht,ht1,hpow,hsep⟩ := choose_smooth_scale 0 hε he
  simp only [Nat.zero_add,pow_one,scaleConstant,Nat.cast_one,mul_one] at hpow hsep
  let h : Gap := ⟨t,ht,by linarith⟩
  refine ⟨h,ht1,hpow,?_⟩
  have ht4 : t < 1 / 4 := by linarith
  have h16 : (16 : ℝ) ≤ 1 / t := (le_div_iff₀ ht).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) h16
  have hlog16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num,Real.log_pow]
    norm_num
  rw [hlog16] at hlog
  have hquarter : Real.log (1 / (4 * t)) = Real.log (1 / t) - Real.log 4 := by
    rw [Real.log_div one_ne_zero (mul_ne_zero (by norm_num) ht.ne'),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) ht.ne',
      Real.log_div one_ne_zero ht.ne']
    ring
  change ε < modulus uniformGaps t / 32
  rw [uniformGaps_modulus ht ht4,hquarter]
  have hb : 2 * ε < t / 8 * Real.log (1 / t) := hsep
  have hc := mul_le_mul_of_nonneg_left hlog ht.le
  nlinarith

end ThresholdHC.ContinuousObserved
