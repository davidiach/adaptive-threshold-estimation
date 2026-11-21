import ThresholdHC.DepthLegendre.Specification

/-! Rodrigues-formula facts for `legendre n = (2^n n!)⁻¹ dⁿ/dxⁿ (x²-1)ⁿ`, used by
`lem:poly` of `research/2026-10-27-nonlinear-population/upper/proof-body.tex`
(lines 36-54 and 67-69): the Legendre differential equation, the coefficients and their
parity, the degree, `P_n(1) = 1`, and the slope `c = P_{2K+1}'(0)` with
`|c| ≥ 1`. -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open Polynomial

/-- Leibniz rule for a factor `X`. -/
theorem rodrigues_leibniz_X (m : ℕ) (g : ℝ[X]) :
    derivative^[m+1] (X * g) = X * derivative^[m+1] g + ((m:ℝ[X])+1) * derivative^[m] g := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Function.iterate_succ_apply' derivative (m+1) (X*g), ih]
    simp only [Function.iterate_succ_apply', derivative_add, derivative_mul, derivative_X,
      derivative_natCast, derivative_one]
    push_cast
    ring

/-- Leibniz rule for a factor `X²-1`. -/
theorem rodrigues_leibniz_sq (m : ℕ) (g : ℝ[X]) :
    derivative^[m+2] ((X^2 - 1) * g) = (X^2 - 1) * derivative^[m+2] g +
      2 * ((m:ℝ[X])+2) * X * derivative^[m+1] g +
      ((m:ℝ[X])+2) * ((m:ℝ[X])+1) * derivative^[m] g := by
  have hC : (C 2 : ℝ[X]) = 2 := map_ofNat C 2
  induction m with
  | zero =>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, derivative_mul,
      derivative_sub, derivative_X_pow, derivative_one, derivative_add, derivative_C,
      Nat.cast_zero]
    simp [hC]
    ring
  | succ m ih =>
    rw [Function.iterate_succ_apply' derivative (m+2) ((X^2-1)*g), ih]
    simp only [Function.iterate_succ_apply', derivative_add, derivative_mul, derivative_X,
      derivative_natCast, derivative_one, derivative_sub, derivative_X_pow, derivative_ofNat]
    push_cast
    simp [hC]
    ring

/-- `(x²-1) f' = 2n x f` for `f = (x²-1)ⁿ`. -/
theorem rodrigues_key (n : ℕ) :
    (X^2 - 1 : ℝ[X]) * derivative ((X^2-1 : ℝ[X])^n) = C (2*(n:ℝ)) * (X * (X^2-1)^n) := by
  rw [derivative_pow]
  have hC : (C 2 : ℝ[X]) = 2 := map_ofNat C 2
  cases n with
  | zero => simp
  | succ n =>
    simp only [derivative_sub, derivative_X_pow, derivative_one, map_mul, hC, Nat.add_sub_cancel]
    simp [hC, pow_succ]
    ring

/-- The differential equation for `dⁿ/dxⁿ (x²-1)ⁿ`. -/
theorem rodrigues_ode (n : ℕ) :
    (X^2-1 : ℝ[X]) * derivative (derivative (derivative^[n] ((X^2-1 : ℝ[X])^n))) +
      2 * X * derivative (derivative^[n] ((X^2-1 : ℝ[X])^n)) -
      ((n:ℝ[X]) * ((n:ℝ[X])+1)) * derivative^[n] ((X^2-1 : ℝ[X])^n) = 0 := by
  cases n with
  | zero => simp
  | succ m =>
    have h := congrArg (derivative^[m+2]) (rodrigues_key (m+1))
    rw [rodrigues_leibniz_sq, iterate_derivative_C_mul, rodrigues_leibniz_X (m+1)] at h
    set f := ((X^2-1 : ℝ[X])^(m+1)) with hf
    have e1 : derivative^[m] (derivative f) = derivative^[m+1] f := rfl
    have e2 : derivative^[m+1] (derivative f) = derivative (derivative^[m+1] f) :=
      Function.iterate_succ_apply' _ _ _
    have e3 : derivative^[m+2] (derivative f) =
        derivative (derivative (derivative^[m+1] f)) := by
      rw [← e2]; exact Function.iterate_succ_apply' _ _ _
    have e4 : derivative^[m+2] f = derivative (derivative^[m+1] f) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2, e3, e4] at h
    have hc : (C (2*((m+1 : ℕ):ℝ)) : ℝ[X]) = 2*((m:ℝ[X])+1) := by
      simp [map_ofNat]
    rw [hc] at h
    push_cast at h ⊢
    linear_combination h

/-- The Legendre differential equation `(x²-1)P'' + 2xP' - n(n+1)P = 0`. -/
theorem legendre_ode (n : ℕ) :
    (X^2-1) * derivative^[2] (legendre n) + 2*X * derivative (legendre n) -
      C ((n:ℝ)*(n+1)) * legendre n = 0 := by
  have h := rodrigues_ode n
  have hC : (C ((n:ℝ)*(n+1)) : ℝ[X]) = (n:ℝ[X]) * ((n:ℝ[X])+1) := by simp
  rw [hC]
  simp only [legendre, iterate_derivative_C_mul, derivative_C_mul]
  show (X^2-1) * (C _ * derivative (derivative _)) + _ - _ = 0
  linear_combination (C ((2 ^ n * (n.factorial : ℝ))⁻¹)) * h

theorem rodrigues_base_expand (n : ℕ) :
    ((X^2-1 : ℝ[X])^n) = expand ℝ 2 ((X + C (-1))^n) := by
  simp [sub_eq_add_neg]

/-- Only even coefficients of `(x²-1)ⁿ` survive. -/
theorem rodrigues_base_coeff (n j : ℕ) :
    ((X^2-1 : ℝ[X])^n).coeff j =
      if 2 ∣ j then (-1:ℝ)^(n - j/2) * (n.choose (j/2) : ℝ) else 0 := by
  rw [rodrigues_base_expand, coeff_expand (by norm_num), coeff_X_add_C_pow]

theorem legendre_coeff (n m : ℕ) :
    (legendre n).coeff m = (2 ^ n * (n.factorial : ℝ))⁻¹ * ((m+n).descFactorial n : ℝ) *
      ((X^2-1 : ℝ[X])^n).coeff (m+n) := by
  rw [legendre, coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul, mul_assoc]

theorem legendre_coeff_of_odd (n m : ℕ) (h : ¬ 2 ∣ (m+n)) : (legendre n).coeff m = 0 := by
  rw [legendre_coeff, rodrigues_base_coeff]
  simp [h]

theorem legendre_coeff_of_even (n m i : ℕ) (h : m + n = 2*i) :
    (legendre n).coeff m = (2 ^ n * (n.factorial : ℝ))⁻¹ * ((m+n).descFactorial n : ℝ) *
      ((-1:ℝ)^(n - i) * (n.choose i : ℝ)) := by
  have hd : 2 ∣ m + n := ⟨i, h⟩
  rw [legendre_coeff, rodrigues_base_coeff]
  simp only [hd, ↓reduceIte]
  rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

/-- `P_{2K+1}` is odd: its even coefficients vanish. -/
theorem legendre_coeff_even (K i : ℕ) : (legendre (2*K+1)).coeff (2*i) = 0 :=
  legendre_coeff_of_odd _ _ (by omega)

theorem legendre_coeff_self (n : ℕ) : (legendre n).coeff n ≠ 0 := by
  rw [legendre_coeff_of_even n n n (by ring), Nat.sub_self, pow_zero, Nat.choose_self]
  have h1 : ((n+n).descFactorial n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega)
  simp [h1, Nat.factorial_ne_zero]

theorem legendre_natDegree (n : ℕ) : (legendre n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ (legendre_coeff_self n)
  have hb : (X^2-1 : ℝ[X]).natDegree ≤ 2 := by
    have := natDegree_X_pow_sub_C (n := 2) (R := ℝ) (1:ℝ)
    rw [map_one] at this
    omega
  have hf : ((X^2-1 : ℝ[X])^n).natDegree ≤ 2*n := by
    refine natDegree_pow_le.trans ?_
    nlinarith
  refine (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative _ _).trans ?_)
  omega

/-- `P_n(1) = 1`: only the term differentiating `(x-1)ⁿ` fully survives at `1`. -/
theorem legendre_eval_one (n : ℕ) : (legendre n).eval 1 = 1 := by
  have hf : ((X^2-1 : ℝ[X])^n) = (X - C 1)^n * (X - C (-1))^n := by
    rw [← mul_pow]; congr 1; simp; ring
  have hD : (derivative^[n] ((X^2-1 : ℝ[X])^n)).eval 1 = n.factorial * 2^n := by
    rw [hf, iterate_derivative_mul, eval_finsetSum, Finset.sum_eq_single 0]
    · simp only [Nat.choose_zero_right, Nat.sub_zero, iterate_derivative_X_sub_pow_self,
        Function.iterate_zero_apply, one_smul, eval_mul, eval_natCast, eval_pow, eval_sub, eval_X,
        eval_C]
      norm_num
    · intro k hk hk0
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [iterate_derivative_X_sub_pow, show n - (n - k) = k by omega]
      simp [zero_pow hk0]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  rw [legendre, eval_mul, eval_C, hD]
  have : (2 ^ n * (n.factorial : ℝ)) ≠ 0 := by positivity
  field_simp

/-- `c = P'_{2K+1}(0)` is the linear coefficient of `P_{2K+1}`. -/
theorem depthSlope_eq_coeff (K : ℕ) : depthSlope K = (legendre (2*K+1)).coeff 1 := by
  rw [depthSlope, ← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

/-- `c = (-1)^K (K+1) C(2K+1,K) / 4^K`. -/
theorem depthSlope_formula (K : ℕ) :
    depthSlope K = (-1:ℝ)^K * (((K:ℝ)+1) * ((2*K+1).choose K : ℝ)) / 4^K := by
  rw [depthSlope_eq_coeff, legendre_coeff_of_even (2*K+1) 1 (K+1) (by ring),
    show 2*K+1-(K+1) = K by omega, Nat.choose_symm_half]
  have hd : ((1 + (2*K+1)).descFactorial (2*K+1) : ℝ) =
      (2*(K:ℝ)+2) * ((2*K+1).factorial : ℝ) := by
    have h := Nat.factorial_mul_descFactorial (n := 1 + (2*K+1)) (k := 2*K+1) (by omega)
    rw [show 1 + (2*K+1) - (2*K+1) = 1 by omega, Nat.factorial_one, one_mul,
      show 1 + (2*K+1) = (2*K+1) + 1 by ring, Nat.factorial_succ] at h
    rw [show 1 + (2*K+1) = (2*K+1) + 1 by ring, h]
    push_cast
    ring
  rw [hd]
  have hf : ((2*K+1).factorial : ℝ) ≠ 0 := by positivity
  have h4 : (4:ℝ)^K ≠ 0 := by positivity
  rw [pow_succ, pow_mul]
  field_simp
  ring

/-- `|c| ≥ 1`, from `4^K ≤ (K+1) C(2K+1,K)`. -/
theorem abs_depthSlope_ge_one (K : ℕ) : 1 ≤ |depthSlope K| := by
  have hc : (0:ℝ) < ((2*K+1).choose K : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  rw [depthSlope_formula, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (mul_pos (by positivity) hc : (0:ℝ) < ((K:ℝ)+1) * ((2*K+1).choose K : ℝ)),
    abs_of_pos (by positivity : (0:ℝ) < 4^K), le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast Nat.four_pow_le_add_one_mul_choose K

theorem depthSlope_ne_zero (K : ℕ) : depthSlope K ≠ 0 := by
  intro h
  have := abs_depthSlope_ge_one K
  rw [h, abs_zero] at this
  norm_num at this

end ThresholdHC.DepthLegendre
