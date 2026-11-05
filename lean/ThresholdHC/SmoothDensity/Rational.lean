import Mathlib

noncomputable section
open scoped ContDiff
namespace ThresholdHC.SmoothDensity

/-- A rational profile whose rescalings perturb the sign probability smoothly. -/
def profile (x : ℝ) : ℝ := x / (x ^ 2 + 1)

theorem profile_contDiff : ContDiff ℝ ∞ profile :=
  contDiff_id.div ((contDiff_id.pow 2).add contDiff_const)
    (fun x => ne_of_gt (by positivity))

private theorem shift_ne_zero (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

private def complexDerivative (k : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ k * k.factorial / ((x : ℂ) + Complex.I) ^ (k + 1)

private theorem complexDerivative_hasDeriv (k : ℕ) (x : ℝ) :
    HasDerivAt (complexDerivative k) (complexDerivative (k + 1) x) x := by
  have hi : HasDerivAt (fun y : ℝ => (y : ℂ) + Complex.I) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt.add_const Complex.I
  have hd := ((hi.pow (k + 1)).inv (pow_ne_zero _ (shift_ne_zero x))).const_mul
    ((-1 : ℂ) ^ k * k.factorial)
  convert hd using 1
  · funext y
    simp [complexDerivative, div_eq_mul_inv]
  · dsimp [complexDerivative]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ (-1 : ℂ)]
    simp only [mul_one]
    field_simp [shift_ne_zero]
    ring

theorem profile_iteratedDeriv (k : ℕ) (x : ℝ) :
    iteratedDeriv k profile x = (complexDerivative k x).re := by
  induction k generalizing x with
  | zero =>
    simp [profile, complexDerivative, Complex.normSq_apply, pow_two]
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      (complexDerivative_hasDeriv k x)).deriv

theorem profile_derivative_bound (k : ℕ) (x : ℝ) :
    |iteratedDeriv k profile x| ≤ k.factorial := by
  rw [profile_iteratedDeriv]
  apply (Complex.abs_re_le_norm _).trans
  have hn : 1 ≤ ‖(x : ℂ) + Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((x : ℂ) + Complex.I)
  have hp : 1 ≤ ‖(x : ℂ) + Complex.I‖ ^ (k + 1) := one_le_pow₀ hn
  simp only [complexDerivative, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_natCast]
  exact div_le_self (by positivity) hp

end ThresholdHC.SmoothDensity
