import ThresholdHC.DepthLegendre.Rodrigues

/-! The polynomial `u_K = c⁻¹ · divX P_{2K+1}` of `lem:poly` in
`research/2026-10-27-nonlinear-population/upper/proof-body.tex` (lines 20-34,
56-59): `P_{2K+1} = c x u_K`, so `u_K(x) = P_{2K+1}(x)/(c x)` off zero and
`u_K(0) = 1`; `u_K` is even of degree `2K`, `u_K'(0) = 0`, `u_K(1) = 1/c`, and
`u_K` satisfies `x(1-x²)u'' + (2-4x²)u' + λ x u = 0` with `λ = 4K²+6K`. -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open Polynomial

theorem legendre_coeff_zero (K : ℕ) : (legendre (2*K+1)).coeff 0 = 0 := by
  simpa using legendre_coeff_even K 0

theorem legendre_eq_X_mul_divX (K : ℕ) :
    legendre (2*K+1) = X * (legendre (2*K+1)).divX := by
  have h := X_mul_divX_add (legendre (2*K+1))
  rw [legendre_coeff_zero, map_zero, add_zero] at h
  exact h.symm

/-- `P_{2K+1} = c X u_K` as polynomials. -/
theorem legendre_eq_depth (K : ℕ) :
    legendre (2*K+1) = C (depthSlope K) * X * depthPolynomial K := by
  have hc := depthSlope_ne_zero K
  have h1 : C (depthSlope K) * C (depthSlope K)⁻¹ = (1 : ℝ[X]) := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  conv_lhs => rw [legendre_eq_X_mul_divX K]
  rw [depthPolynomial]
  linear_combination (-(X * (legendre (2*K+1)).divX)) * h1

theorem legendre_eval_depth (K : ℕ) (x : ℝ) :
    (legendre (2*K+1)).eval x = depthSlope K * x * (depthPolynomial K).eval x := by
  rw [legendre_eq_depth K]
  simp only [eval_mul, eval_C, eval_X]

theorem depthPolynomial_eval_of_ne (K : ℕ) (x : ℝ) (hx : x ≠ 0) :
    (depthPolynomial K).eval x = (legendre (2*K+1)).eval x / (depthSlope K * x) := by
  have hc := depthSlope_ne_zero K
  rw [legendre_eval_depth]
  field_simp

theorem depthPolynomial_eval_zero (K : ℕ) : (depthPolynomial K).eval 0 = 1 := by
  have hc := depthSlope_ne_zero K
  rw [depthPolynomial, eval_mul, eval_C, ← coeff_zero_eq_eval_zero, coeff_divX, zero_add,
    ← depthSlope_eq_coeff, inv_mul_cancel₀ hc]

theorem depthPolynomial_coeff (K m : ℕ) :
    (depthPolynomial K).coeff m = (depthSlope K)⁻¹ * (legendre (2*K+1)).coeff (m+1) := by
  rw [depthPolynomial, coeff_C_mul, coeff_divX]

theorem depthPolynomial_coeff_odd (K i : ℕ) : (depthPolynomial K).coeff (2*i+1) = 0 := by
  rw [depthPolynomial_coeff, show 2*i+1+1 = 2*(i+1) by ring, legendre_coeff_even, mul_zero]

/-- `u_K` is even. -/
theorem depthPolynomial_even (K : ℕ) (x : ℝ) :
    (depthPolynomial K).eval (-x) = (depthPolynomial K).eval x := by
  rw [eval_eq_sum_range, eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rcases Nat.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr, ← two_mul, pow_mul, pow_mul, neg_sq]
  · rw [hr, depthPolynomial_coeff_odd, zero_mul, zero_mul]

theorem depthPolynomial_natDegree (K : ℕ) : (depthPolynomial K).natDegree = 2*K := by
  rw [depthPolynomial, natDegree_C_mul (inv_ne_zero (depthSlope_ne_zero K)),
    natDegree_divX_eq_natDegree_tsub_one, legendre_natDegree, Nat.add_sub_cancel]

theorem depthPolynomial_derivative_eval_zero (K : ℕ) :
    (derivative (depthPolynomial K)).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add]
  have := depthPolynomial_coeff_odd K 0
  rw [mul_zero, zero_add] at this
  rw [this, zero_mul]

theorem depthPolynomial_eval_one (K : ℕ) :
    (depthPolynomial K).eval 1 = (depthSlope K)⁻¹ := by
  have hc := depthSlope_ne_zero K
  have h := legendre_eval_depth K 1
  rw [legendre_eval_one, mul_one, mul_comm] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- The differential equation of `u_K`, `λ = n(n+1)-2 = 4K²+6K`. -/
theorem depthPolynomial_ode (K : ℕ) (x : ℝ) :
    x * (1 - x^2) * (derivative (derivative (depthPolynomial K))).eval x +
      (2 - 4*x^2) * (derivative (depthPolynomial K)).eval x +
      (4*(K:ℝ)^2 + 6*K) * x * (depthPolynomial K).eval x = 0 := by
  have hc := depthSlope_ne_zero K
  have h := congrArg (eval x) (legendre_ode (2*K+1))
  rw [legendre_eq_depth K] at h
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, derivative_mul,
    derivative_add, derivative_C, derivative_X, zero_mul, zero_add, mul_one, eval_mul, eval_add,
    eval_sub, eval_C, eval_X, eval_pow, eval_one, eval_zero, eval_ofNat] at h
  push_cast at h
  apply mul_left_cancel₀ hc
  linear_combination (-1) * h

end ThresholdHC.DepthLegendre
