import Mathlib

/-! Positive distinct finite magnitudes admit an odd-polynomial interpolant
of the constant target. This is the sufficient-direction algebra behind the
cap threshold; statistical count-law equivalence is a separate obligation. -/

noncomputable section
open Polynomial
open scoped BigOperators

namespace ThresholdHC.CapIdentification

theorem positive_square_injective {m : ℕ} (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (hi : Function.Injective d) : Function.Injective (fun i => (d i)^2) := by
  intro i j h
  exact hi ((sq_eq_sq₀ (hd i).le (hd j).le).mp h)

theorem odd_interpolation {m : ℕ} (d : Fin m → ℝ) (hd : ∀ i, 0 < d i) (hi : Function.Injective d) :
    ∃ a : Fin m → ℝ, ∀ i : Fin m, (∑ j : Fin m, a j*(d i)^(2*j.val+1)) = 1 := by
  classical
  by_cases hm : m = 0
  · subst m
    exact ⟨fun _ => 0,fun i => Fin.elim0 i⟩
  have hm' : 0 < m := Nat.pos_of_ne_zero hm
  let Q := Lagrange.interpolate Finset.univ (fun i : Fin m => (d i)^2) (fun i => (d i)⁻¹)
  have hinj := (positive_square_injective d hd hi).injOn (s := (Finset.univ : Finset (Fin m)))
  have hdegree : Q.natDegree < m := by
    by_cases hQ : Q = 0
    · simpa only [hQ,natDegree_zero] using hm'
    · apply (natDegree_lt_iff_degree_lt hQ).mpr
      simpa only [Finset.card_univ,Fintype.card_fin] using
        Lagrange.degree_interpolate_lt (fun i => (d i)⁻¹) hinj
  refine ⟨fun j => Q.coeff j.val, ?_⟩
  intro i
  have heval : Q.eval ((d i)^2) = (d i)⁻¹ :=
    Lagrange.eval_interpolate_at_node (fun i => (d i)⁻¹) hinj (Finset.mem_univ i)
  calc
    _ = d i*Q.eval ((d i)^2) := by
      rw [eval_eq_sum_range' hdegree,
        ← Fin.sum_univ_eq_sum_range (fun j : ℕ => Q.coeff j*((d i)^2)^j) m,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add,pow_mul]
      ring
    _ = 1 := by rw [heval,mul_inv_cancel₀ (hd i).ne']

theorem finite_moment_target_identified {m : ℕ} (d w g : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (hi : Function.Injective d)
    (hmom : ∀ j : Fin m, (∑ i : Fin m, w i*g i*(d i)^(2*j.val+1)) = 0) :
    (∑ i : Fin m, w i*g i) = 0 := by
  obtain ⟨a,ha⟩ := odd_interpolation d hd hi
  calc
    _ = ∑ i : Fin m, w i*g i*(∑ j : Fin m, a j*(d i)^(2*j.val+1)) := by simp only [ha,mul_one]
    _ = ∑ j : Fin m, a j*(∑ i : Fin m, w i*g i*(d i)^(2*j.val+1)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp only [hmom,mul_zero,Finset.sum_const_zero]

theorem cap_threshold_equivalence (N m : ℕ) (hm : 0 < m) :
    m ≤ (N+1)/2 ↔ 2*m-1 ≤ N := by omega

end ThresholdHC.CapIdentification
