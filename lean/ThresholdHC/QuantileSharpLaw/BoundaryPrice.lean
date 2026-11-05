import ThresholdHC.QuantileSharpLaw.InteractionGrowth
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Real
namespace ThresholdHC.QuantileSharpLaw

theorem boundary_scalar_price {N D c : ℝ} (hN : 0 ≤ N) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hbound : N ≤ D+2*c+max 0 (c-1)*sqrt D) :
    1+sqrt N ≤ sqrt 2*(sqrt (1+D)+c) := by
  have hr : 1 ≤ sqrt (1+D) := one_le_sqrt.mpr (by linarith)
  have hd : sqrt D ≤ sqrt (1+D) := sqrt_le_sqrt (by linarith)
  have hrad : 1+N ≤ (sqrt (1+D)+c)^2 := by
    by_cases hc1 : c ≤ 1
    · rw [max_eq_left (by linarith),zero_mul,add_zero] at hbound
      have hm := mul_le_mul_of_nonneg_left hr hc
      nlinarith only [hbound,hm,sq_sqrt (show 0 ≤ 1+D by linarith),sq_nonneg c]
    · rw [max_eq_right (by linarith)] at hbound
      have hm := mul_le_mul_of_nonneg_left (add_le_add hr hd) hc
      have hc2 : c ≤ c^2 := by nlinarith only [hc1]
      nlinarith only [hbound,hm,hc2,sqrt_nonneg D,sq_sqrt (show 0 ≤ 1+D by linarith)]
  apply (sq_le_sq₀ (by positivity : 0 ≤ 1+sqrt N)
    (by positivity : 0 ≤ sqrt 2*(sqrt (1+D)+c))).mp
  rw [mul_pow,sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith only [hrad,sq_sqrt hN,sq_nonneg (sqrt N-1)]

theorem unselected_boundary_price {A E B H c N : ℝ}
    (hA : 0 ≤ A) (hAE : A ≤ E) (hB : 0 ≤ B) (hBc : B ≤ c)
    (hHc : H ≤ 2*c) (hN : 0 ≤ N)
    (hinteraction : N ≤ E+H+costInteraction A B) :
    1+sqrt N ≤ sqrt 2*(sqrt (1+(E+costInteraction A 1))+c) := by
  let D := E+costInteraction A 1
  have hc : 0 ≤ c := hB.trans hBc
  have hE : 0 ≤ E := hA.trans hAE
  have hI : 0 ≤ costInteraction A 1 := costInteraction_nonneg hA (by norm_num)
  have hD : 0 ≤ D := add_nonneg hE hI
  apply boundary_scalar_price hN hD hc
  by_cases hc1 : c ≤ 1
  · rw [max_eq_left (by linarith),zero_mul,add_zero]
    have hm := costInteraction_monotoneOn hA hB (show (0 : ℝ) ≤ 1 by norm_num) (hBc.trans hc1)
    dsimp [D]
    linarith only [hm,hinteraction,hHc]
  · have hc1' : 1 ≤ c := (lt_of_not_ge hc1).le
    rw [max_eq_right (by linarith)]
    have hm := costInteraction_monotoneOn hA hB hc hBc
    have hg := costInteraction_increment hA hc1'
    have hs : sqrt A ≤ sqrt D := sqrt_le_sqrt (by dsimp [D]; linarith)
    have hscale := mul_le_mul_of_nonneg_left hs (show 0 ≤ c-1 by linarith)
    dsimp [D] at *
    nlinarith only [hm,hg,hinteraction,hHc,hscale]

end ThresholdHC.QuantileSharpLaw
