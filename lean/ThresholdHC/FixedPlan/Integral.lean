import ThresholdHC.FixedPlan.Tail

/-! The uniform-law identity
`2 integral_0^(1/2) P(Bin(2k+1,p) ≥ k+1) dp = binom(2k+2,k+1)/2^(2k+3)
= 1/(2(k+1) Beta(k+1,1/2))`.

The tail is a sum of Bernstein polynomials, whose derivative telescopes to
`(2k+1) binom(2k,k) (p(1-p))^k`. Integration by parts uses the explicit
antiderivative `T(p)(p-1/2) + (2k+1) binom(2k,k) (p(1-p))^(k+1)/(2(k+1))`. -/

noncomputable section
open MeasureTheory Polynomial

namespace ThresholdHC.FixedPlan
open ThresholdHC.Tier6

theorem tail_derivative (k : ℕ) :
    derivative (∑ ν ∈ Finset.Ico (k+1) (2*k+2), bernsteinPolynomial ℝ (2*k+1) ν) =
      ((2*k+1 : ℕ) : ℝ[X]) * bernsteinPolynomial ℝ (2*k) k := by
  rw [map_sum, Finset.sum_Ico_eq_sum_range, show 2*k+2-(k+1) = k+1 by omega]
  have h : ∀ i ∈ Finset.range (k+1), derivative (bernsteinPolynomial ℝ (2*k+1) (k+1+i)) =
      ((2*k+1 : ℕ) : ℝ[X]) *
        (bernsteinPolynomial ℝ (2*k) (k+i) - bernsteinPolynomial ℝ (2*k) (k+(i+1))) := by
    intro i _
    rw [show k+1+i = (k+i)+1 by omega, bernsteinPolynomial.derivative_succ, Nat.add_sub_cancel]
    rfl
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum,
    Finset.sum_range_sub' (fun i => bernsteinPolynomial ℝ (2*k) (k+i)),
    bernsteinPolynomial.eq_zero_of_lt ℝ (show 2*k < k+(k+1) by omega)]
  simp

theorem tail_eval (k : ℕ) (x : ℝ) :
    (∑ ν ∈ Finset.Ico (k+1) (2*k+2), bernsteinPolynomial ℝ (2*k+1) ν).eval x = majorityTail k x := by
  simp [majorityTail, bernsteinPolynomial, Polynomial.eval_finsetSum]

/-- `d/dp P(Bin(2k+1,p) ≥ k+1) = (2k+1) binom(2k,k) (p(1-p))^k`. -/
theorem hasDerivAt_majorityTail (k : ℕ) (p : ℝ) :
    HasDerivAt (majorityTail k) ((2*k+1 : ℝ) * ((2*k).choose k : ℝ) * (p*(1-p))^k) p := by
  have hP := (∑ ν ∈ Finset.Ico (k+1) (2*k+2), bernsteinPolynomial ℝ (2*k+1) ν).hasDerivAt p
  have he : (fun x => (∑ ν ∈ Finset.Ico (k+1) (2*k+2), bernsteinPolynomial ℝ (2*k+1) ν).eval x) =
      majorityTail k := funext (tail_eval k)
  rw [he, tail_derivative] at hP
  convert hP using 1
  simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]
  rw [show 2*k - k = k by omega, mul_pow]
  push_cast
  ring

/-- An antiderivative of the majority tail. -/
theorem hasDerivAt_tail_antiderivative (k : ℕ) (p : ℝ) :
    HasDerivAt (fun x => majorityTail k x * (x - 1/2) +
      (2*k+1 : ℝ) * ((2*k).choose k : ℝ) * (x*(1-x))^(k+1) / (2*((k : ℝ)+1)))
      (majorityTail k p) p := by
  have h1 : HasDerivAt (fun x => majorityTail k x * (x - 1/2))
      ((2*k+1 : ℝ) * ((2*k).choose k : ℝ) * (p*(1-p))^k * (p - 1/2) + majorityTail k p * 1) p :=
    (hasDerivAt_majorityTail k p).mul ((hasDerivAt_id p).sub_const (1/2 : ℝ))
  have hq : HasDerivAt (fun x : ℝ => x*(1-x)) (1*(1-p) + p*(0-1)) p :=
    (hasDerivAt_id p).mul ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p))
  have h2 : HasDerivAt (fun x : ℝ => (x*(1-x))^(k+1))
      (((k+1 : ℕ) : ℝ) * (p*(1-p))^(k+1-1) * (1*(1-p) + p*(0-1))) p := hq.pow (k+1)
  have h3 : HasDerivAt (fun x : ℝ => (2*k+1 : ℝ) * ((2*k).choose k : ℝ) * (x*(1-x))^(k+1) / (2*((k : ℝ)+1)))
      ((2*k+1 : ℝ) * ((2*k).choose k : ℝ) *
        (((k+1 : ℕ) : ℝ) * (p*(1-p))^(k+1-1) * (1*(1-p) + p*(0-1))) / (2*((k : ℝ)+1))) p :=
    (h2.const_mul _).div_const _
  convert h1.add h3 using 1
  rw [Nat.add_sub_cancel]
  have hk : ((k : ℝ)+1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem majorityTail_zero (k : ℕ) : majorityTail k 0 = 0 := by
  unfold majorityTail
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j ≠ 0 := by
    simp only [Finset.mem_Ico] at hj
    omega
  simp [zero_pow hj']

/-- `integral_0^(1/2) P(Bin(2k+1,p) ≥ k+1) dp = (2k+1) binom(2k,k) / (2(k+1) 4^(k+1))`. -/
theorem integral_majorityTail (k : ℕ) :
    (∫ p in (0:ℝ)..(1/2), majorityTail k p) =
      (2*k+1 : ℝ) * ((2*k).choose k : ℝ) / (2*((k : ℝ)+1) * 4^(k+1)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_tail_antiderivative k x)
    ((continuous_majorityTail k).intervalIntegrable _ _)]
  simp only [majorityTail_zero]
  have hk : (2*((k : ℝ)+1)) ≠ 0 := by positivity
  have h4 : ((1:ℝ)/2 * (1 - 1/2))^(k+1) = 1 / 4^(k+1) := by
    rw [show (1:ℝ)/2 * (1 - 1/2) = 1/4 by norm_num, div_pow, one_pow]
  rw [h4]
  simp only [sub_self, mul_zero, zero_add, zero_mul, zero_sub, ne_eq, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, mul_zero, zero_div, sub_zero]
  field_simp

/-- `(k+1) binom(2k+2,k+1) = 2(2k+1) binom(2k,k)` over the reals. -/
theorem choose_succ_central (k : ℕ) :
    ((k : ℝ)+1) * ((2*(k+1)).choose (k+1) : ℝ) = 2*(2*k+1) * ((2*k).choose k : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  exact_mod_cast h

/-- `2 integral_0^(1/2) I_p(a,a) dp = binom(2a,a)/2^(2a+1)` with `a = k+1`. -/
theorem uniform_tail_integral (k : ℕ) :
    2 * (∫ p in (0:ℝ)..(1/2), majorityTail k p) =
      ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1) := by
  rw [integral_majorityTail]
  have hk : ((k : ℝ)+1) ≠ 0 := by positivity
  have hB : ((2*(k+1)).choose (k+1) : ℝ) = 2*(2*k+1) * ((2*k).choose k : ℝ) / ((k : ℝ)+1) := by
    rw [eq_div_iff hk, mul_comm]
    exact choose_succ_central k
  have h2 : (2:ℝ)^(2*(k+1)+1) = 2 * 4^(k+1) := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2, hB]
  have h4 : (0:ℝ) < 4^(k+1) := by positivity
  generalize (4:ℝ)^(k+1) = t at *
  field_simp

/-- At the uniform gap law, `e_m = binom(2a,a)/2^(2a+1)` with `a = k+1`. -/
theorem uniform_meanMajorityMiss (k : ℕ) :
    meanMajorityMiss Genie.uniformGapLaw k = ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1) := by
  have h := Genie.uniformGap_integral (fun x => majorityTail k (1/2 - x))
  unfold meanMajorityMiss majorityMiss
  refine h.trans ?_
  rw [intervalIntegral.integral_comp_sub_left (fun x => majorityTail k x) (1/2 : ℝ)]
  rw [show (1/2 : ℝ) - 1/2 = 0 by norm_num, sub_zero]
  exact uniform_tail_integral k

theorem choose_mul_factorial_central (k : ℕ) :
    (2*(k+1)).choose (k+1) * (k+1).factorial = 2^(k+1) * (2*k+1).doubleFactorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k+1 ≤ 2*(k+1) by omega)
  rw [show 2*(k+1) - (k+1) = k+1 by omega] at h1
  have h2 := Nat.factorial_eq_mul_doubleFactorial (2*k+1)
  have h3 := Nat.doubleFactorial_two_mul (k+1)
  rw [show 2*k+1+1 = 2*(k+1) by ring, h3] at h2
  rw [h2] at h1
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (k+1))
  rw [h1]
  ring

/-- `binom(2a,a)/2^(2a+1) = 1/(2a Beta(a,1/2))` with `a = k+1`. -/
theorem uniform_beta (k : ℕ) :
    ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1) =
      1 / (2 * ((k : ℝ)+1) * ProbabilityTheory.beta ((k : ℝ)+1) (1/2)) := by
  unfold ProbabilityTheory.beta
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_one_half_eq, Real.Gamma_nat_add_one_add_half]
  have hn : ((2*(k+1)).choose (k+1) : ℝ) * (((k : ℝ)+1) * (k.factorial : ℝ)) =
      2^(k+1) * ((2*k+1).doubleFactorial : ℝ) := by
    have h := choose_mul_factorial_central k
    rw [Nat.factorial_succ] at h
    exact_mod_cast h
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hd : ((2*k+1).doubleFactorial : ℝ) ≠ 0 := by
    have := Nat.doubleFactorial_pos (2*k+1)
    positivity
  have hk : ((k : ℝ)+1) ≠ 0 := by positivity
  have hB : ((2*(k+1)).choose (k+1) : ℝ) =
      2^(k+1) * ((2*k+1).doubleFactorial : ℝ) / (((k : ℝ)+1) * (k.factorial : ℝ)) := by
    rw [eq_div_iff (mul_ne_zero hk hf)]
    exact hn
  have h2 : (2:ℝ)^(2*(k+1)+1) = 2 * 2^(k+1) * 2^(k+1) := by ring
  rw [h2, hB]
  have ht : (0:ℝ) < 2^(k+1) := by positivity
  generalize (2:ℝ)^(k+1) = t at *
  field_simp

end ThresholdHC.FixedPlan
