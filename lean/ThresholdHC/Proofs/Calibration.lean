import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

theorem negbin_total : ThresholdHC.Targets.negbin_total := by
  intro p hp hp1
  have hr : ‖1-p‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr).mul_left (p ^ 2)
  have hpn : p ≠ 0 := ne_of_gt hp
  have heq : p ^ 2 * (1 / (1 - (1-p)) ^ (1+1)) = 1 := by field_simp; ring
  rw [heq] at hs
  convert hs.tsum_eq using 1
  congr 1
  funext k
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  ring

theorem negbin_mean : ThresholdHC.Targets.negbin_mean := by
  intro p hp hp1
  have hr : ‖1-p‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).mul_left (2 * p ^ 2)
  have hpn : p ≠ 0 := ne_of_gt hp
  have heq : 2 * p ^ 2 * (1 / (1 - (1-p)) ^ (2+1)) = 2/p := by field_simp; ring
  rw [heq] at hs
  convert hs.tsum_eq using 1
  congr 1
  funext k
  rw [Nat.cast_choose_two]
  push_cast
  ring

theorem haldane_inverse_moment : ThresholdHC.Targets.haldane_inverse_moment := by
  intro p hp hp1
  have hs := (hasSum_geometric_of_lt_one (show 0 ≤ 1-p by linarith) (show 1-p < 1 by linarith)).mul_left (p ^ 2)
  have hpn : p ≠ 0 := ne_of_gt hp
  have heq : p ^ 2 * (1 - (1-p))⁻¹ = p := by simp only [sub_sub_cancel]; field_simp [hpn]
  rw [heq] at hs
  convert hs.tsum_eq using 1
  congr 1
  funext k
  have hk : (k : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp

end ThresholdHC.Proofs
