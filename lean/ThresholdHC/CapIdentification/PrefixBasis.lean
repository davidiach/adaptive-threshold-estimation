import Mathlib

/-! The likelihood polynomials of depth-N binary prefixes span every
polynomial of degree at most N. The proof uses marginalization and charges
no statistical identification or compactness assumption. -/

noncomputable section
open Polynomial
open scoped BigOperators

namespace ThresholdHC.CapIdentification

def prefixPolynomial (n k : ℕ) : ℝ[X] := X^k*(1-X)^(n-k)

theorem prefixPolynomial_elevation (n k : ℕ) (hk : k ≤ n) :
    prefixPolynomial n k = prefixPolynomial (n+1) k+prefixPolynomial (n+1) (k+1) := by
  unfold prefixPolynomial
  rw [show n+1-k = (n-k)+1 by omega,show n+1-(k+1) = n-k by omega,pow_succ,pow_succ]
  ring

theorem prefixPolynomial_diagonal (n : ℕ) : prefixPolynomial n n = (X:ℝ[X])^n := by
  simp [prefixPolynomial]

theorem prefixPolynomial_degree (n k : ℕ) (hk : k ≤ n) : (prefixPolynomial n k).natDegree ≤ n := by
  have hm := natDegree_mul_le (p := (X:ℝ[X])^k) (q := (1-X)^(n-k))
  have h1 : ((1-X):ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hp := (natDegree_pow_le (p := (1-X:ℝ[X])) (n := n-k)).trans
    (Nat.mul_le_mul_left (n-k) h1)
  simp only [natDegree_X_pow,mul_one] at hm hp
  change (X^k*(1-X)^(n-k):ℝ[X]).natDegree ≤ n
  omega

theorem annihilates_prefixes_below (F : ℝ[X] →ₗ[ℝ] ℝ) (N : ℕ)
    (hF : ∀ k, k ≤ N → F (prefixPolynomial N k) = 0) :
    ∀ n, n ≤ N → ∀ k, k ≤ n → F (prefixPolynomial n k) = 0 := by
  induction N with
  | zero =>
    intro n hn k hk
    have hn0 : n = 0 := by omega
    subst n
    exact hF k hk
  | succ N ih =>
    have hprev (k : ℕ) (hk : k ≤ N) : F (prefixPolynomial N k) = 0 := by
      rw [prefixPolynomial_elevation N k hk,map_add,hF k (by omega),hF (k+1) (by omega),add_zero]
    intro n hn k hk
    by_cases he : n = N+1
    · subst n
      exact hF k hk
    · exact ih hprev n (by omega) k hk

theorem annihilates_prefix_iff (F : ℝ[X] →ₗ[ℝ] ℝ) (N : ℕ) :
    (∀ k, k ≤ N → F (prefixPolynomial N k) = 0) ↔
      ∀ P : ℝ[X], P.natDegree ≤ N → F P = 0 := by
  constructor
  · intro hF P hP
    have hmon (j : ℕ) (hj : j ≤ N) : F ((X:ℝ[X])^j) = 0 := by
      rw [← prefixPolynomial_diagonal]
      exact annihilates_prefixes_below F N hF j hj j le_rfl
    rw [P.as_sum_range_C_mul_X_pow]
    simp only [C_mul',map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hmon j (by have h := Finset.mem_range.mp hj; omega),mul_zero]
  · intro hF k hk
    exact hF _ (prefixPolynomial_degree N k hk)

end ThresholdHC.CapIdentification
