import ThresholdHC.DepthLegendre.Energy

/-! The moments of `lem:poly` in
`research/2026-10-27-nonlinear-population/upper/proof-body.tex` (lines 71-84),
by a route different from the source's. Instead of `n`-fold integration by parts
on `[-1,1]` and the recurrence `P'_{n+1} - P'_{n-1} = (2n+1) P_n`, a Green identity
on `[0,1]` from the Legendre equation: for every polynomial `g`,
`∫₀¹ (n(n+1) g + (1-x²) g'' - 2x g') P_n = g(0) P_n'(0)`, because
`W = (1-x²)(g P_n' - g' P_n)` has `W' = -(n(n+1) g + (1-x²) g'' - 2x g') P_n`,
`W(1) = 0` and `P_n(0) = 0`. With `g = 1`, `x` and `x^(m+2)` this gives
`∫₀¹ P_n = c/(n(n+1))` and `∫₀¹ x^(2j+1) P_n = 0` for `j < K`, hence the
orthogonality and the value `m_K` of `∫₀¹ 2x u_K`. The section ends with the
assembled statement of `lem:poly`. -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open Polynomial Set

theorem legendre_ode_eval (K : ℕ) (x : ℝ) :
    (x^2 - 1) * (derivative (derivative (legendre (2*K+1)))).eval x +
      2 * x * (derivative (legendre (2*K+1))).eval x -
      (2*(K:ℝ)+1) * (2*K+2) * (legendre (2*K+1)).eval x = 0 := by
  have h := congrArg (eval x) (legendre_ode (2*K+1))
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, eval_mul, eval_add,
    eval_sub, eval_C, eval_X, eval_pow, eval_one, eval_zero, eval_ofNat] at h
  push_cast at h
  linear_combination h

theorem legendre_eval_zero (K : ℕ) : (legendre (2*K+1)).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, legendre_coeff_zero]

/-- The Green identity on `[0,1]` for the Legendre equation. -/
theorem legendre_green (K : ℕ) (g : ℝ[X]) :
    ∫ x in (0:ℝ)..1, ((2*(K:ℝ)+1) * (2*K+2) * g.eval x +
        (1 - x^2) * (derivative (derivative g)).eval x - 2 * x * (derivative g).eval x) *
        (legendre (2*K+1)).eval x = g.eval 0 * depthSlope K := by
  set P := legendre (2*K+1) with hP
  have hW : ∀ x : ℝ, HasDerivAt
      (fun y => (1 - y^2) * (g.eval y * (derivative P).eval y - (derivative g).eval y * P.eval y))
      (-(((2*(K:ℝ)+1) * (2*K+2) * g.eval x +
        (1 - x^2) * (derivative (derivative g)).eval x - 2 * x * (derivative g).eval x) *
        P.eval x)) x := by
    intro x
    have hx : HasDerivAt (fun y : ℝ => 1 - y^2) (-(2*x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub 1
    have h := hx.mul (((g.hasDerivAt x).mul ((derivative P).hasDerivAt x)).sub
      (((derivative g).hasDerivAt x).mul (P.hasDerivAt x)))
    convert h using 1
    have hode := legendre_ode_eval K x
    rw [← hP] at hode
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (g.eval x) * hode
  have hcont : Continuous (fun x : ℝ => ((2*(K:ℝ)+1) * (2*K+2) * g.eval x +
      (1 - x^2) * (derivative (derivative g)).eval x - 2 * x * (derivative g).eval x) *
      P.eval x) := by
    have := g.continuous
    have := (derivative g).continuous
    have := (derivative (derivative g)).continuous
    have := P.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hW x)
    (hcont.neg.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_neg] at hint
  have h0 : P.eval 0 = 0 := legendre_eval_zero K
  have hc : (derivative P).eval 0 = depthSlope K := rfl
  simp only [one_pow, sub_self, zero_mul, zero_pow two_ne_zero, sub_zero, one_mul, h0,
    mul_zero, hc] at hint
  linarith

theorem continuous_mul_legendre (K m : ℕ) :
    Continuous (fun x : ℝ => x^m * (legendre (2*K+1)).eval x) :=
  (continuous_pow m).mul (legendre (2*K+1)).continuous

/-- `n(n+1) ∫₀¹ P_n = c`. -/
theorem legendre_integral (K : ℕ) :
    (2*(K:ℝ)+1) * (2*K+2) * ∫ x in (0:ℝ)..1, (legendre (2*K+1)).eval x = depthSlope K := by
  have h := legendre_green K 1
  simp only [eval_one, derivative_one, derivative_zero, eval_zero, mul_zero, add_zero, sub_zero,
    mul_one, one_mul] at h
  rw [← intervalIntegral.integral_const_mul]
  exact h

/-- `(n(n+1) - 2) ∫₀¹ x P_n = 0`. -/
theorem legendre_moment_one (K : ℕ) :
    ((2*(K:ℝ)+1) * (2*K+2) - 2) * ∫ x in (0:ℝ)..1, x^1 * (legendre (2*K+1)).eval x = 0 := by
  have h := legendre_green K X
  simp only [eval_X, derivative_X, derivative_one, eval_zero, eval_one, mul_zero, add_zero,
    mul_one, zero_mul] at h
  rw [← intervalIntegral.integral_const_mul]
  refine Eq.trans ?_ h
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  ring

/-- `(n(n+1) - (m+2)(m+3)) ∫₀¹ x^(m+2) P_n + (m+2)(m+1) ∫₀¹ x^m P_n = 0`. -/
theorem legendre_moment_step (K m : ℕ) :
    ((2*(K:ℝ)+1) * (2*K+2) - ((m:ℝ)+2) * (m+3)) *
        (∫ x in (0:ℝ)..1, x^(m+2) * (legendre (2*K+1)).eval x) +
      ((m:ℝ)+2) * (m+1) * (∫ x in (0:ℝ)..1, x^m * (legendre (2*K+1)).eval x) = 0 := by
  have h := legendre_green K (X^(m+2))
  simp only [derivative_X_pow, eval_pow, eval_X, derivative_C_mul_X_pow, eval_mul, eval_C,
    zero_pow (Nat.succ_ne_zero (m+1)), zero_mul] at h
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add]
  · refine Eq.trans ?_ h
    apply intervalIntegral.integral_congr
    intro x _
    simp only [show m + 2 - 1 = m + 1 by omega]
    push_cast
    ring
  · exact (continuous_const.mul (continuous_mul_legendre K (m+2))).intervalIntegrable 0 1
  · exact (continuous_const.mul (continuous_mul_legendre K m)).intervalIntegrable 0 1

/-- The odd moments `∫₀¹ x^(2j+1) P_{2K+1}` vanish for `j < K`. -/
theorem legendre_odd_moment (K : ℕ) (hK : 1 ≤ K) :
    ∀ j < K, ∫ x in (0:ℝ)..1, x^(2*j+1) * (legendre (2*K+1)).eval x = 0 := by
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  intro j
  induction j with
  | zero =>
    intro _
    have h := legendre_moment_one K
    have hne : ((2*(K:ℝ)+1) * (2*K+2) - 2) ≠ 0 := by nlinarith
    simpa using (mul_eq_zero.mp h).resolve_left hne
  | succ j ih =>
    intro hj
    have h := legendre_moment_step K (2*j+1)
    rw [ih (by omega), mul_zero, add_zero] at h
    have hj' : ((j:ℝ)+1) + 1 ≤ K := by exact_mod_cast hj
    have hne : ((2*(K:ℝ)+1) * (2*K+2) - (((2*j+1 : ℕ) : ℝ)+2) * ((2*j+1 : ℕ)+3)) ≠ 0 := by
      push_cast
      nlinarith
    have := (mul_eq_zero.mp h).resolve_left hne
    rw [show 2*j+1+2 = 2*(j+1)+1 by ring] at this
    exact this

/-- `∫₀¹ x^(2j+2) u_K = c⁻¹ ∫₀¹ x^(2j+1) P_{2K+1}`. -/
theorem depthPolynomial_moment (K j : ℕ) :
    ∫ x in (0:ℝ)..1, x^(2*j+2) * (depthPolynomial K).eval x =
      (depthSlope K)⁻¹ * ∫ x in (0:ℝ)..1, x^(2*j+1) * (legendre (2*K+1)).eval x := by
  have hc := depthSlope_ne_zero K
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [legendre_eval_depth]
  field_simp
  ring

theorem depthPolynomial_orthogonal (K : ℕ) (hK : 1 ≤ K) :
    ∀ j < K, ∫ x in (0:ℝ)..1, x^(2*j+2) * (depthPolynomial K).eval x = 0 := by
  intro j hj
  rw [depthPolynomial_moment, legendre_odd_moment K hK j hj, mul_zero]

theorem depthPolynomial_first_moment (K : ℕ) :
    ∫ x in (0:ℝ)..1, 2*x*(depthPolynomial K).eval x = depthMoment K := by
  have hc := depthSlope_ne_zero K
  have h := legendre_integral K
  have he : ∫ x in (0:ℝ)..1, 2*x*(depthPolynomial K).eval x =
      2 * (depthSlope K)⁻¹ * ∫ x in (0:ℝ)..1, (legendre (2*K+1)).eval x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [legendre_eval_depth]
    field_simp
  have hN : (2*(K:ℝ)+1) * (2*K+2) ≠ 0 := by positivity
  have hI : ∫ x in (0:ℝ)..1, (legendre (2*K+1)).eval x =
      depthSlope K / ((2*(K:ℝ)+1) * (2*K+2)) := by
    rw [eq_div_iff hN, mul_comm]
    exact h
  rw [he, hI, depthMoment]
  field_simp

/-- `lem:poly`, assembled. -/
theorem depthPolynomialFacts : DepthPolynomialStatement := by
  intro K hK
  exact ⟨depthSlope_ne_zero K, depthPolynomial_eval_of_ne K, depthPolynomial_eval_zero K,
    depthPolynomial_natDegree K, depthPolynomial_even K, abs_depthPolynomial_le_one K hK,
    depthPolynomial_orthogonal K hK, depthPolynomial_first_moment K⟩

end ThresholdHC.DepthLegendre
