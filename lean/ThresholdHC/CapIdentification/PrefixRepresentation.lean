import ThresholdHC.CapIdentification.CenteredBasis
import ThresholdHC.CapIdentification.ContrastFunctional

/-! Actual coefficient representations in the depth-N likelihood basis,
including a polynomial representing any linear combination of the observed
odd moments. -/

noncomputable section
open Polynomial Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification

theorem polynomial_mem_prefix_span (N : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ N) :
    P ∈ Submodule.span ℝ (range (fun k : Fin (N+1) => prefixPolynomial N k.val)) := by
  by_contra h
  obtain ⟨F,hF,hker⟩ := Submodule.exists_le_ker_of_notMem h
  apply hF
  apply (annihilates_prefix_iff F N).mp ?_ P hP
  intro k hk
  exact hker (Submodule.subset_span ⟨⟨k,by omega⟩,rfl⟩)

theorem exists_prefix_coefficients (N : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ N) :
    ∃ a : Fin (N+1) → ℝ, P = ∑ k : Fin (N+1), a k • prefixPolynomial N k.val := by
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (polynomial_mem_prefix_span N P hP)
  exact ⟨a,ha.symm⟩

theorem exists_count_coefficients (N : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ N) :
    ∃ y : Fin (N+1) → ℝ, P = ∑ k : Fin (N+1),
      (y k*(N.choose k.val:ℝ)) • prefixPolynomial N k.val := by
  obtain ⟨a,ha⟩ := exists_prefix_coefficients N P hP
  refine ⟨fun k => a k/(N.choose k.val:ℝ),?_⟩
  convert ha using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [div_mul_cancel₀]
  exact_mod_cast (Nat.choose_pos (by have hk := k.isLt; omega)).ne'

def oddMomentRepresentative (N : ℕ) (w : Fin ((N+1)/2) → ℝ) : ℝ[X] :=
  ∑ j, (w j/2) • centeredPower (1/2) (2*j.val+1)

theorem oddMomentRepresentative_degree (N : ℕ) (w : Fin ((N+1)/2) → ℝ) :
    (oddMomentRepresentative N w).natDegree ≤ N := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_smul_le _ _).trans ((centeredPower_degree _ _).trans (by have hj := j.isLt; omega))

theorem oddMomentRepresentative_difference (N : ℕ) (w : Fin ((N+1)/2) → ℝ) (d : ℝ) :
    (oddMomentRepresentative N w).eval (1/2+d)-(oddMomentRepresentative N w).eval (1/2-d) =
      ∑ j, w j*d^(2*j.val+1) := by
  simp only [oddMomentRepresentative,eval_finsetSum,eval_smul,smul_eq_mul,
    centeredPower_eval_plus,centeredPower_eval_minus,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have ho : Odd (2*j.val+1) := ⟨j.val,rfl⟩
  rw [ho.neg_pow]
  ring

end ThresholdHC.CapIdentification
