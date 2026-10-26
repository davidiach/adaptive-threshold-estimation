import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

theorem scaling_up_pointwise : ThresholdHC.Targets.scaling_up_pointwise := by
  intro c h x hc hh hx
  by_cases hratio : h / x ≤ 1
  · rw [min_eq_right hratio]
    simpa [mul_div_assoc] using (min_le_right (1 : ℝ) (c * h / x))
  · rw [min_eq_left (le_of_not_ge hratio)]
    simpa using le_trans (min_le_left (1 : ℝ) (c * h / x)) hc

theorem scaling_down_pointwise : ThresholdHC.Targets.scaling_down_pointwise := by
  intro b h x hb hble hh hx
  apply le_min
  · calc
      b * min 1 (h / x) ≤ b * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hb)
      _ ≤ 1 := by simpa using hble
  · simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (h / x)) (le_of_lt hb)

theorem modulus_scaling_up : ThresholdHC.Targets.modulus_scaling_up := by
  sorry

theorem power_modulus_critical : ThresholdHC.Targets.power_modulus_critical := by
  sorry

theorem power_modulus : ThresholdHC.Targets.power_modulus := by
  sorry

end ThresholdHC.Proofs
