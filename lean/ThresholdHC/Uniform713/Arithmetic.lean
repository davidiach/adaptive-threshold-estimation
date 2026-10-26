import ThresholdHC.Proofs.Constants

/-!
Scalar lemmas used by the full uniform variance-work development.
These do not formalize the stopping-time, Hoeffding, geometric-series,
unbiasedness, or integration arguments in UNIFORM_PRODUCT_BOUND.md.
This module is additional evidence and earns no frozen-target points.
-/

namespace ThresholdHC.Uniform713.Arithmetic
open ThresholdHC Real

theorem error_prefactor_lt : Real.exp (-2) + (2/3)*Real.exp (-(1/2 : ℝ)) < 3/5 := by
  have he2 : 7 < Real.exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2 by norm_num) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  have heh : (8/5 : ℝ) < Real.exp (1/2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num)
    norm_num at h
    linarith
  have hn2 : Real.exp (-2) < (1/7 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_lt_iff_one_lt_mul₀ (Real.exp_pos 2)).2
    linarith
  have hnh : Real.exp (-(1/2 : ℝ)) < (5/8 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_lt_iff_one_lt_mul₀ (Real.exp_pos (1/2))).2
    linarith
  linarith

theorem geometric_second_moment_factor_lt :
    (1/(1-rLevel)) * (1/(1-rLevel)+1/(1-rLevel^3)) < 17 := by
  have h := ThresholdHC.Proofs.constant_second_moment
  change 5/(1-rLevel) * (1/(1-rLevel)+1/(1-rLevel^3)) < 85 at h
  have heq : 5/(1-rLevel) * (1/(1-rLevel)+1/(1-rLevel^3)) =
      5*((1/(1-rLevel)) * (1/(1-rLevel)+1/(1-rLevel^3))) := by ring
  rw [heq] at h
  linarith

theorem fourth_root_three_lt : Real.sqrt (Real.sqrt 3) < (4/3 : ℝ) := by
  have hs := Real.sqrt_nonneg (3:ℝ)
  have hss := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hfour := Real.sq_sqrt hs
  have hfour0 := Real.sqrt_nonneg (Real.sqrt 3)
  have hroot : Real.sqrt 3 < (16/9 : ℝ) := by nlinarith
  nlinarith

theorem second_moment_scalar_lt :
    (Real.sqrt (Real.sqrt 3)) * ((1/(1-rLevel)) *
      (1/(1-rLevel)+1/(1-rLevel^3))) < 23 := by
  have h1 := mul_le_mul_of_nonneg_left geometric_second_moment_factor_lt.le
    (Real.sqrt_nonneg (Real.sqrt 3))
  have h2 := mul_lt_mul_of_pos_right fourth_root_three_lt (show (0:ℝ)<17 by norm_num)
  linarith

theorem survival_coefficients : (125/18 : ℝ) < 7 ∧ (338/49 : ℝ) < 7 := by
  constructor <;> norm_num

theorem work_scalar_lt :
    7*(2+Real.log 2+rLevel*Real.log 2/(1-rLevel)) < 31 := by
  have h := ThresholdHC.Proofs.constant_work
  change 34*(2+Real.log 2+rLevel*Real.log 2/(1-rLevel)) < 149 at h
  linarith

theorem product_of_moment_bounds (I V W : ℝ) (hI : 0 ≤ I) (hW0 : 0 ≤ W)
    (hV : V ≤ 23*I) (hW : W ≤ 31*I) : V*W ≤ 713*I^2 := by
  calc
    V*W ≤ (23*I)*(31*I) := mul_le_mul hV hW hW0 (by positivity)
    _ = 713*I^2 := by ring

end ThresholdHC.Uniform713.Arithmetic

#print axioms ThresholdHC.Uniform713.Arithmetic.error_prefactor_lt

#print axioms ThresholdHC.Uniform713.Arithmetic.geometric_second_moment_factor_lt

#print axioms ThresholdHC.Uniform713.Arithmetic.fourth_root_three_lt

#print axioms ThresholdHC.Uniform713.Arithmetic.second_moment_scalar_lt

#print axioms ThresholdHC.Uniform713.Arithmetic.survival_coefficients

#print axioms ThresholdHC.Uniform713.Arithmetic.work_scalar_lt

#print axioms ThresholdHC.Uniform713.Arithmetic.product_of_moment_bounds
