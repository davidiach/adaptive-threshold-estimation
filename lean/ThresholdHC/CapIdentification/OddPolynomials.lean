import ThresholdHC.CapIdentification.Interpolation

/-! An odd polynomial with L allowed monomials cannot equal one at more than
L positive points. Rolle's theorem produces positive derivative roots, whose
squares are roots of a polynomial of degree at most L-1. -/

noncomputable section
open Polynomial Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification

def oddPolynomial {L : ℕ} (a : Fin L → ℝ) : ℝ[X] :=
  ∑ j : Fin L, C (a j)*X^(2*j.val+1)

def derivativeCore {L : ℕ} (a : Fin L → ℝ) : ℝ[X] :=
  ∑ j : Fin L, C (a j*(2*j.val+1))*X^j.val

theorem oddPolynomial_eval {L : ℕ} (a : Fin L → ℝ) (x : ℝ) :
    (oddPolynomial a).eval x = ∑ j : Fin L, a j*x^(2*j.val+1) := by
  simp only [oddPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]

theorem oddPolynomial_eval_zero {L : ℕ} (a : Fin L → ℝ) : (oddPolynomial a).eval 0 = 0 := by
  simp [oddPolynomial_eval]

theorem oddPolynomial_derivative_eval {L : ℕ} (a : Fin L → ℝ) (x : ℝ) :
    (oddPolynomial a).derivative.eval x = (derivativeCore a).eval (x^2) := by
  simp only [oddPolynomial,derivativeCore,derivative_sum,derivative_C_mul_X_pow,
    eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,Nat.add_one_sub_one]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rw [pow_mul]

theorem derivativeCore_degree_le {L : ℕ} (a : Fin L → ℝ) : (derivativeCore a).natDegree ≤ L-1 := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ j.val).trans (by omega)

theorem odd_level_card_le {L : ℕ} (a : Fin L → ℝ) (S : Finset ℝ)
    (hpos : ∀ x ∈ S, 0 < x) (hval : ∀ x ∈ S, (oddPolynomial a).eval x = 1) : S.card ≤ L := by
  classical
  by_cases hS : S.Nonempty
  swap
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty] using Nat.zero_le L
  obtain ⟨x,hx⟩ := hS
  have hd : (oddPolynomial a).derivative ≠ 0 := by
    intro hz
    have he : (oddPolynomial a).eval x = (oddPolynomial a).eval 0 := by
      rw [eq_C_of_derivative_eq_zero hz]
      simp
    rw [hval x hx,oddPolynomial_eval_zero] at he
    norm_num at he
  have hcore : derivativeCore a ≠ 0 := by
    intro hz
    apply hd
    apply Polynomial.funext
    intro y
    rw [oddPolynomial_derivative_eval,hz,eval_zero,eval_zero]
  have hL : 0 < L := by
    by_contra h
    have h0 : L = 0 := by omega
    subst L
    simp [derivativeCore] at hcore
  let T := (oddPolynomial a).derivative.roots.toFinset.filter (fun y => 0 < y)
  have hinter : S.card ≤ T.card+1 := by
    apply Finset.card_le_of_interleaved
    intro u hu v hv huv _
    obtain ⟨y,hy,hy'⟩ := exists_deriv_eq_zero huv (oddPolynomial a).continuousOn
      ((hval u hu).trans (hval v hv).symm)
    refine ⟨y, ?_, hy⟩
    dsimp only [T]
    rw [Finset.mem_filter,Multiset.mem_toFinset,mem_roots hd,IsRoot,← (oddPolynomial a).deriv]
    exact ⟨hy',lt_trans (hpos u hu) hy.1⟩
  have hinj : Set.InjOn (fun y : ℝ => y^2) (↑T : Set ℝ) := by
    intro u hu v hv huv
    exact (sq_eq_sq₀ (Finset.mem_filter.mp hu).2.le (Finset.mem_filter.mp hv).2.le).mp huv
  have hsub : T.image (fun y => y^2) ⊆ (derivativeCore a).roots.toFinset := by
    intro y hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset,mem_roots hcore,IsRoot,← oddPolynomial_derivative_eval]
    exact isRoot_of_mem_roots (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hu).1)
  have hcard : T.card ≤ (derivativeCore a).natDegree := by
    calc
      T.card = (T.image (fun y => y^2)).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ (derivativeCore a).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (derivativeCore a).roots.card := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
  have hdeg := derivativeCore_degree_le a
  omega

end ThresholdHC.CapIdentification
