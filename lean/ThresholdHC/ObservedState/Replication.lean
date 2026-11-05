import ThresholdHC.ObservedState.Targets

noncomputable section
open MeasureTheory
namespace ThresholdHC.ObservedState

variable {I : Type} [Fintype I]

def replicatedWeight (w : I → ℝ) (M : ℕ) (i : I × Fin M) : ℝ := w i.1 / M

theorem replicated_sum (w : I → ℝ) {M : ℕ} (hM : 0 < M) :
    (∑ i : I × Fin M, replicatedWeight w M i) = ∑ i, w i := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [replicatedWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem replicated_moment (w f : I → ℝ) {M : ℕ} (hM : 0 < M) :
    (∑ i : I × Fin M, replicatedWeight w M i * f i.1) = ∑ i, w i * f i := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [replicatedWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem replicated_square_sum (w : I → ℝ) {M : ℕ} (hM : 0 < M) :
    (∑ i : I × Fin M, (replicatedWeight w M i) ^ 2) = (∑ i, (w i) ^ 2) / M := by
  rw [Fintype.sum_prod_type,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [replicatedWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem replicated_square_le (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1)
    {M : ℕ} (hM : 0 < M) :
    (∑ i : I × Fin M, (replicatedWeight w M i) ^ 2) ≤ 1 / M := by
  rw [replicated_square_sum w hM]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) => hw i)
  rwa [hs,one_pow] at h

theorem replication_count {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ 1 / (M : ℝ) ≤ δ * Δ ^ 2 / 16 := by
  obtain ⟨M,hM⟩ := exists_nat_gt (16 / (δ * Δ ^ 2))
  have hM0 : (0 : ℝ) < M := (div_pos (by norm_num) (by positivity)).trans hM
  refine ⟨M,by exact_mod_cast hM0,?_⟩
  have h := (div_lt_iff₀ (by positivity : 0 < δ * Δ ^ 2)).mp hM
  apply (div_le_iff₀ hM0).mpr
  nlinarith

end ThresholdHC.ObservedState
