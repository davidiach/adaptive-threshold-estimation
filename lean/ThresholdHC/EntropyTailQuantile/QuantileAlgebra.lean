import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The scalar step producing the manuscript's exact `1 + 2√2` comparison
factor. The integral and entropy premises must be established separately. -/

namespace ThresholdHC.EntropyTailQuantile
open Real

theorem quantile_comparison_algebra {x y T Q : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hTS : T ≤ x+y)
    (hQ : Q ≤ T + sqrt 2*x + sqrt (8*T*y)) :
    Q ≤ (1+2*sqrt 2)*(x+y) := by
  have hs : sqrt (8*T*y) ≤ sqrt 2*(x+2*y) := by
    apply (sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hprod := mul_le_mul_of_nonneg_right hTS hy
    nlinarith [sq_nonneg x]
  have hroot : 0 ≤ sqrt 2 := sqrt_nonneg 2
  nlinarith only [hQ, hs, hTS]

theorem quantile_comparison_factor_lt_four : 1+2*sqrt 2 < (4:ℝ) := by
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := sqrt_nonneg (2:ℝ)
  nlinarith

end ThresholdHC.EntropyTailQuantile
