import ThresholdHC.Tier6.AlgorithmCore

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Tier6

theorem ofReal_square_rpow_half (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (x^2) ^ (1/2 : ℝ) = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_pow hx]
  simpa only [Nat.cast_ofNat, one_div] using
    ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) (ENNReal.ofReal x)

theorem rms_of_squared_lower {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) (f : Ω → ℝ) (a b Δ : ℝ) (hΔ : 0 ≤ Δ)
    (h : ENNReal.ofReal (Δ^2/16) ≤ max (squaredRisk P f a) (squaredRisk Q f b)) :
    ENNReal.ofReal (Δ/4) ≤ max (rootMeanRisk P f a) (rootMeanRisk Q f b) := by
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ENNReal.max_rpow (by norm_num : (0:ℝ) ≤ 1/2)] at hh
  have heq : Δ^2/16 = (Δ/4)^2 := by ring
  rw [heq, ofReal_square_rpow_half (Δ/4) (by positivity)] at hh
  exact hh

end ThresholdHC.Tier6
