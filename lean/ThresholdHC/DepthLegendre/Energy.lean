import ThresholdHC.DepthLegendre.Polynomial

/-! The sup bound `|u_K| ≤ 1` on `[0,1]` of `lem:poly` in
`research/2026-10-27-nonlinear-population/upper/proof-body.tex` (lines 56-69), by
the source's energy argument. The energy `H = u_K² + (1-x²)u_K'²/λ` satisfies
`x H' = (6x²-4) u_K'²/λ`, so it decreases on `[0, √(2/3)]` and increases on
`[√(2/3), 1]`; hence `H ≤ max (H 0) (H 1) = max 1 (1/c²) = 1` and `u_K² ≤ H`. -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open Polynomial Set

/-- The energy `H(x) = u_K(x)² + (1-x²) u_K'(x)²/λ`, `λ = 4K²+6K`. -/
def depthEnergy (K : ℕ) (x : ℝ) : ℝ :=
  (depthPolynomial K).eval x ^ 2 +
    (1 - x^2) * (derivative (depthPolynomial K)).eval x ^ 2 / (4*(K:ℝ)^2 + 6*K)

theorem hasDerivAt_depthEnergy (K : ℕ) (x : ℝ) :
    HasDerivAt (depthEnergy K)
      (2 * (depthPolynomial K).eval x * (derivative (depthPolynomial K)).eval x +
        ((-2*x) * (derivative (depthPolynomial K)).eval x ^ 2 +
          (1 - x^2) * (2 * (derivative (depthPolynomial K)).eval x *
            (derivative (derivative (depthPolynomial K))).eval x)) / (4*(K:ℝ)^2 + 6*K)) x := by
  have h0 := (depthPolynomial K).hasDerivAt x
  have h1 := (derivative (depthPolynomial K)).hasDerivAt x
  have hx : HasDerivAt (fun y : ℝ => 1 - y^2) (-(2*x)) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub 1
  have h := (h0.pow 2).add ((hx.mul (h1.pow 2)).div_const (4*(K:ℝ)^2 + 6*K))
  unfold depthEnergy
  convert h using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.pow_apply]
  ring

/-- `x H'(x) = (6x²-4) u_K'(x)²/λ`, from the differential equation of `u_K`. -/
theorem depthEnergy_deriv_identity (K : ℕ) (hK : 1 ≤ K) (x : ℝ) :
    x * (2 * (depthPolynomial K).eval x * (derivative (depthPolynomial K)).eval x +
        ((-2*x) * (derivative (depthPolynomial K)).eval x ^ 2 +
          (1 - x^2) * (2 * (derivative (depthPolynomial K)).eval x *
            (derivative (derivative (depthPolynomial K))).eval x)) / (4*(K:ℝ)^2 + 6*K)) =
      (6*x^2 - 4) * (derivative (depthPolynomial K)).eval x ^ 2 / (4*(K:ℝ)^2 + 6*K) := by
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hl : (4*(K:ℝ)^2 + 6*K) ≠ 0 := by positivity
  have hode := depthPolynomial_ode K x
  field_simp
  linear_combination (2 * (derivative (depthPolynomial K)).eval x) * hode

theorem depthEnergy_deriv_sign (K : ℕ) (hK : 1 ≤ K) (x : ℝ) (hx : 0 < x) :
    (x^2 ≤ 2/3 → deriv (depthEnergy K) x ≤ 0) ∧ (2/3 ≤ x^2 → 0 ≤ deriv (depthEnergy K) x) := by
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hl : 0 < (4*(K:ℝ)^2 + 6*K) := by positivity
  rw [(hasDerivAt_depthEnergy K x).deriv]
  have hid := depthEnergy_deriv_identity K hK x
  set D := 2 * (depthPolynomial K).eval x * (derivative (depthPolynomial K)).eval x +
        ((-2*x) * (derivative (depthPolynomial K)).eval x ^ 2 +
          (1 - x^2) * (2 * (derivative (depthPolynomial K)).eval x *
            (derivative (derivative (depthPolynomial K))).eval x)) / (4*(K:ℝ)^2 + 6*K)
  set w := (derivative (depthPolynomial K)).eval x
  constructor
  · intro h2
    have hn : (6*x^2 - 4) * w ^ 2 / (4*(K:ℝ)^2 + 6*K) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg w))
        hl.le
    rw [← hid] at hn
    by_contra hD
    linarith [mul_pos hx (lt_of_not_ge hD)]
  · intro h2
    have hn : 0 ≤ (6*x^2 - 4) * w ^ 2 / (4*(K:ℝ)^2 + 6*K) :=
      div_nonneg (mul_nonneg (by linarith) (sq_nonneg w)) hl.le
    rw [← hid] at hn
    by_contra hD
    linarith [mul_neg_of_pos_of_neg hx (lt_of_not_ge hD)]

theorem depthEnergy_zero (K : ℕ) : depthEnergy K 0 = 1 := by
  simp [depthEnergy, depthPolynomial_eval_zero, depthPolynomial_derivative_eval_zero]

theorem depthEnergy_one (K : ℕ) : depthEnergy K 1 ≤ 1 := by
  have hc := abs_depthSlope_ge_one K
  have hc0 := depthSlope_ne_zero K
  simp only [depthEnergy, depthPolynomial_eval_one, one_pow, sub_self, zero_mul, zero_div,
    add_zero, inv_pow]
  apply inv_le_one_of_one_le₀
  rw [← sq_abs]
  nlinarith

theorem depthEnergy_le_one (K : ℕ) (hK : 1 ≤ K) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    depthEnergy K x ≤ 1 := by
  set s := Real.sqrt (2/3) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = 2/3 := Real.sq_sqrt (by norm_num)
  have hs1 : s ≤ 1 := by nlinarith
  have hcont : ∀ D : Set ℝ, ContinuousOn (depthEnergy K) D :=
    fun D y _ => (hasDerivAt_depthEnergy K y).continuousAt.continuousWithinAt
  have hdiff : ∀ D : Set ℝ, DifferentiableOn ℝ (depthEnergy K) D :=
    fun D y _ => (hasDerivAt_depthEnergy K y).differentiableAt.differentiableWithinAt
  rcases le_total x s with hxs | hxs
  · have hanti : AntitoneOn (depthEnergy K) (Icc 0 s) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s) (hcont _) (hdiff _)
      intro y hy
      rw [interior_Icc] at hy
      exact (depthEnergy_deriv_sign K hK y hy.1).1 (by nlinarith [hy.1, hy.2])
    have := hanti ⟨le_refl 0, hs0⟩ ⟨hx.1, hxs⟩ hx.1
    rw [depthEnergy_zero] at this
    exact this
  · have hmono : MonotoneOn (depthEnergy K) (Icc s 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s 1) (hcont _) (hdiff _)
      intro y hy
      rw [interior_Icc] at hy
      exact (depthEnergy_deriv_sign K hK y (lt_of_le_of_lt hs0 hy.1)).2 (by nlinarith [hy.1, hy.2])
    exact (hmono ⟨hxs, hx.2⟩ ⟨hs1, le_refl 1⟩ hx.2).trans (depthEnergy_one K)

/-- `|u_K| ≤ 1` on `[0,1]`. -/
theorem abs_depthPolynomial_le_one (K : ℕ) (hK : 1 ≤ K) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    |(depthPolynomial K).eval x| ≤ 1 := by
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hl : 0 < (4*(K:ℝ)^2 + 6*K) := by positivity
  have hH := depthEnergy_le_one K hK x hx
  have hx2 : 0 ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hrest : 0 ≤ (1 - x^2) * (derivative (depthPolynomial K)).eval x ^ 2 /
      (4*(K:ℝ)^2 + 6*K) := div_nonneg (mul_nonneg hx2 (sq_nonneg _)) hl.le
  unfold depthEnergy at hH
  rw [← sq_le_one_iff_abs_le_one]
  linarith

end ThresholdHC.DepthLegendre
