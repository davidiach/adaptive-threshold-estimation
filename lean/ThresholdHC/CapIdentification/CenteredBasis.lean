import ThresholdHC.CapIdentification.PrefixBasis

/-! Centered polynomial moments and depth-N likelihoods carry the same linear
information. For a sign contrast, even centered powers vanish and the remaining
constraints are exactly the first ceiling(N/2) odd moments. -/

noncomputable section
open Polynomial
open scoped BigOperators

namespace ThresholdHC.CapIdentification

def centeredPower (a : ℝ) (k : ℕ) : ℝ[X] := (X-C a)^k

theorem centeredPower_degree (a : ℝ) (k : ℕ) : (centeredPower a k).natDegree ≤ k := by
  have h : (X-C a:ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  exact (natDegree_pow_le (p := (X-C a:ℝ[X])) (n := k)).trans
    (by simpa only [mul_one] using Nat.mul_le_mul_left k h)

theorem centered_annihilation_iff (F : ℝ[X] →ₗ[ℝ] ℝ) (N : ℕ) (a : ℝ) :
    (∀ k, k ≤ N → F (centeredPower a k) = 0) ↔
      ∀ P : ℝ[X], P.natDegree ≤ N → F P = 0 := by
  constructor
  · intro hF P hP
    let Q := P.comp (X+C a)
    have hQ : Q.natDegree ≤ N := by
      have hd : (X+C a:ℝ[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
      exact natDegree_comp_le.trans ((Nat.mul_le_mul_left P.natDegree hd).trans
        (by simpa only [mul_one] using hP))
    have he : P = Q.comp (X-C a) := by
      dsimp only [Q]
      rw [comp_assoc]
      simp only [add_comp,X_comp,C_comp,sub_add_cancel,comp_X]
    rw [he,Q.as_sum_range_C_mul_X_pow]
    simp only [sum_comp,C_mul',smul_comp,pow_comp,X_comp,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j hj
    have hjN : j ≤ N := by have hh := Finset.mem_range.mp hj; omega
    change Q.coeff j*F (centeredPower a j) = 0
    rw [hF j hjN,mul_zero]
  · intro hF k hk
    exact hF _ ((centeredPower_degree a k).trans hk)

theorem odd_centered_prefix_equivalence (F : ℝ[X] →ₗ[ℝ] ℝ) (N : ℕ) (a : ℝ)
    (heven : ∀ k, k ≤ N → Even k → F (centeredPower a k) = 0) :
    (∀ j : Fin ((N+1)/2), F (centeredPower a (2*j.val+1)) = 0) ↔
      ∀ k, k ≤ N → F (prefixPolynomial N k) = 0 := by
  rw [annihilates_prefix_iff,← centered_annihilation_iff F N a]
  constructor
  · intro hodd k hk
    rcases Nat.even_or_odd k with he | ho
    · exact heven k hk he
    · obtain ⟨j,hj⟩ := ho
      have hj' : k = 2*j+1 := by omega
      have hjN : j < (N+1)/2 := by omega
      simpa only [← hj'] using hodd ⟨j,hjN⟩
  · intro h j
    exact h _ (by have hj := j.isLt; omega)

end ThresholdHC.CapIdentification
