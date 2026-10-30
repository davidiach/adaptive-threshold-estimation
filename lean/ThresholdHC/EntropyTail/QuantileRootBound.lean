import ThresholdHC.EntropyTail.QuantileAlgebra

namespace ThresholdHC.EntropyTail
open Real

theorem quantile_root_bound {h ρ t A C H T y : ℝ}
    (hh : 0 ≤ h) (hρ : 0 ≤ ρ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hcost : C ≤ 2*A + (8/t)*H) (hthreshold : h*ρ/t ≤ T) (hwork : h*H ≤ y) :
    h * sqrt (ρ*C) ≤ sqrt 2 * (h * sqrt (ρ*A)) + sqrt (8*T*y) := by
  have hy : 0 ≤ y := (mul_nonneg hh hH).trans hwork
  have hscaled := mul_le_mul_of_nonneg_left hcost (mul_nonneg (sq_nonneg h) hρ)
  have hprod := mul_le_mul hthreshold hwork (mul_nonneg hh hH) hT
  simp only [div_eq_mul_inv] at hscaled hprod
  have hsA := sq_sqrt (mul_nonneg hρ hA)
  have hsC := sq_sqrt (mul_nonneg hρ hC)
  have hs2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs8 := sq_sqrt (by positivity : 0 ≤ 8*T*y)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [add_sq, mul_pow]
  rw [hsA, hsC, hs2, hs8]
  have hcross : 0 ≤ sqrt 2 * (h * sqrt (ρ*A)) * sqrt (8*T*y) := by positivity
  nlinarith only [hscaled, hprod, hcross]

end ThresholdHC.EntropyTail
