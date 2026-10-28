import ThresholdHC.BlindUpper.CallLaw
import ThresholdHC.Tier6.HardPair

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.Tier6

theorem callScale_eq_modulusIntegrand (L : ℕ) (d : Gap) :
    callScale L d = Real.sqrt ((2 : ℝ)^L)*clippedGap (1/Real.sqrt ((2 : ℝ)^L)) d := by
  have hs : 0 < Real.sqrt ((2 : ℝ)^L) := Real.sqrt_pos.mpr (by positivity)
  unfold callScale clippedGap
  rw [mul_min_of_nonneg _ _ hs.le,mul_one]
  congr 1
  field_simp

theorem callScale_integral_eq_modulus (L : ℕ) (μ : Measure Gap) :
    (∫ d, callScale L d ∂μ) = Real.sqrt ((2 : ℝ)^L)*modulus μ (1/Real.sqrt ((2 : ℝ)^L)) := by
  simp_rw [callScale_eq_modulusIntegrand]
  exact integral_const_mul _ _

theorem clipped_fourth_le {x : ℝ} (hx : 0 ≤ x) : min 1 (x^4) ≤ min 1 x := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    have hx2 : x*x ≤ x := by nlinarith
    have hx4 : x^4 ≤ x := by
      have h := mul_le_mul hx2 hx2 (mul_nonneg hx hx) hx
      nlinarith
    exact (min_le_right _ _).trans hx4
  · rw [min_eq_left (le_of_not_ge hx1)]
    exact min_le_left _ _

theorem inverse_quartic_identity (N d : ℝ) (hN : 0 < N) (hd : 0 < d) :
    ((N*d^2)⁻¹)^2 = ((1/Real.sqrt N)/d)^4 := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  calc
    _ = (((Real.sqrt N)^2*d^2)⁻¹)^2 := by rw [Real.sq_sqrt hN.le]
    _ = _ := by field_simp

theorem callBiasScale_le_modulusIntegrand (L : ℕ) (d : Gap) :
    callBiasScale L d ≤ clippedGap (1/Real.sqrt ((2 : ℝ)^L)) d := by
  unfold callBiasScale clippedGap
  rw [inverse_quartic_identity ((2 : ℝ)^L) d (by positivity) d.property.1]
  exact clipped_fourth_le (div_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) d.property.1.le)

theorem callBiasScale_integral_le_modulus (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    (∫ d, callBiasScale L d ∂μ) ≤ modulus μ (1/Real.sqrt ((2 : ℝ)^L)) :=
  integral_mono (callBiasScale_integrable L μ) (integrable_clippedGap μ (by positivity))
    (callBiasScale_le_modulusIntegrand L)

end ThresholdHC.BlindUpper
