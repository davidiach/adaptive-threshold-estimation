import ThresholdHC.QuantileComparison.Scalar

noncomputable section
open Real
namespace ThresholdHC.QuantileSelection

/-- Absorb the common factor q = h²ρ into the two entropy estimates. -/
theorem core_price {q V Z C T c : ℝ} (hq : 0 ≤ q) (hV : 0 ≤ V) (hZ : 0 ≤ Z)
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hcore : C ≤ V + Z + sqrt (2*V*Z))
    (hwork : q*Z ≤ 2*T*c) :
    sqrt (q*C) ≤ sqrt ((sqrt (q*V))^2 + 2*T*c + 2*sqrt (q*V)*sqrt (T*c)) := by
  have cross : q * sqrt (2*V*Z) = sqrt (q*V) * sqrt (2*(q*Z)) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, sq_sqrt (by positivity : 0 ≤ 2*V*Z),
      sq_sqrt (mul_nonneg hq hV), sq_sqrt (by positivity : 0 ≤ 2*(q*Z))]
    ring
  have hrad : sqrt (2*(q*Z)) ≤ 2*sqrt (T*c) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity), mul_pow, sq_sqrt (mul_nonneg hT hc)]
    linarith
  have hs := mul_le_mul_of_nonneg_left hcore hq
  rw [mul_add, mul_add, cross] at hs
  apply sqrt_le_sqrt
  rw [sq_sqrt (mul_nonneg hq hV)]
  nlinarith only [hs, hwork, mul_le_mul_of_nonneg_left hrad (sqrt_nonneg (q*V))]

/-- The selected tail/core prices share a single Euclidean budget. -/
theorem selection_triangle {T u v x a : ℝ} (hT : 0 ≤ T) (hu : 0 ≤ u) (hx : 0 ≤ x)
    (ha : 0 ≤ a) (htail : T ≤ a+u) (hbudget : u^2+v^2 ≤ x^2) :
    sqrt (T^2+v^2) ≤ x+a := by
  have hux : u ≤ x := (sq_le_sq₀ hu hx).mp (by linarith [sq_nonneg v])
  apply (sq_le_sq₀ (sqrt_nonneg _) (add_nonneg hx ha)).mp
  rw [sq_sqrt (by positivity)]
  nlinarith only [hbudget, pow_le_pow_left₀ hT htail 2, mul_le_mul_of_nonneg_left hux ha]

end ThresholdHC.QuantileSelection
