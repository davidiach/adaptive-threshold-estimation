import Mathlib

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.EntropyTailLower

/-! An algebraic combination step. ComponentLocalization supplies its weighted
budgets, and LocalizedAnnular applies it to actual annular obstructions. -/
theorem finite_component_obstructions {I : Type} [Fintype I]
    (u e v w r : I → ℝ) (B V b C K : ℝ)
    (hu : ∀ i, 0 ≤ u i) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i)
    (hB : 0 < B) (hC : 0 ≤ C) (hK : 0 < K)
    (heBudget : ∑ i, e i ≤ b) (hvBudget : ∑ i, v i ≤ V) (hwBudget : ∑ i, w i ≤ B)
    (hbad : ∀ i, r i/K < e i → u i ≤ r i)
    (hgood : ∀ i, e i ≤ r i/K → (u i)^2*B ≤ C*v i*w i) :
    ∑ i, u i ≤ K*b+sqrt (C*V) := by
  classical
  let G := Finset.univ.filter (fun i => e i ≤ r i/K)
  let H := Finset.univ.filter (fun i => ¬e i ≤ r i/K)
  have hg (i) (hi : i ∈ G) : e i ≤ r i/K := (Finset.mem_filter.mp hi).2
  have hh (i) (hi : i ∈ H) : r i/K < e i := not_le.mp (Finset.mem_filter.mp hi).2
  have hH : ∑ i ∈ H, u i ≤ K*b := by
    calc
      _ ≤ ∑ i ∈ H, K*e i := by
        apply Finset.sum_le_sum
        intro i hi
        have ht := (div_lt_iff₀ hK).mp (hh i hi)
        have hu' := hbad i (hh i hi)
        nlinarith only [ht,hu']
      _ = K*∑ i ∈ H, e i := by rw [Finset.mul_sum]
      _ ≤ K*b := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => he i)).trans heBudget) hK.le
  have hsq : (∑ i ∈ G, u i)^2 ≤ C*V := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul G
      (r := u) (f := fun i => (C/B)*v i) (g := w)
      (fun i _ => mul_nonneg (div_nonneg hC hB.le) (hv i)) (fun i _ => hw i)
      (fun i hi => by
        have ht : (u i)^2 ≤ (C*v i*w i)/B := (le_div_iff₀ hB).mpr (hgood i (hg i hi))
        convert ht using 1
        ring)
    have hvg : ∑ i ∈ G, v i ≤ V :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hv i)).trans hvBudget
    have hwg : ∑ i ∈ G, w i ≤ B :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hw i)).trans hwBudget
    rw [← Finset.mul_sum] at hcs
    have hv0 : 0 ≤ V := (Finset.sum_nonneg (fun i _ => hv i)).trans hvBudget
    have hp := mul_le_mul (mul_le_mul_of_nonneg_left hvg (div_nonneg hC hB.le)) hwg
      (Finset.sum_nonneg (fun i _ => hw i)) (mul_nonneg (div_nonneg hC hB.le) hv0)
    have heq : (C/B*V)*B = C*V := by field_simp
    exact hcs.trans (hp.trans_eq heq)
  have hG : ∑ i ∈ G, u i ≤ sqrt (C*V) := by
    have hn : 0 ≤ ∑ i ∈ G, u i := Finset.sum_nonneg (fun i _ => hu i)
    have hv0 : 0 ≤ V := (Finset.sum_nonneg (fun i _ => hv i)).trans hvBudget
    have hs := sq_sqrt (mul_nonneg hC hv0)
    nlinarith [sqrt_nonneg (C*V)]
  have hsplit : (∑ i, u i) = (∑ i ∈ G, u i)+(∑ i ∈ H, u i) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [hsplit]
  linarith

end ThresholdHC.EntropyTailLower
