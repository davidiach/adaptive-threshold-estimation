import ThresholdHC.Statements2

noncomputable section
namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

theorem sum_deltaK (k1 k2 : ℝ) (L : ℕ) {M : ℕ} (x : Fin M → Bool) :
    ∑ l ∈ Finset.range (L + 1), deltaK k1 k2 l x = zK k1 k2 L x := by
  induction L with
  | zero => simp [deltaK]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [deltaK, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    ring

theorem lemma7_telescoping : ThresholdHC.Targets.lemma7_telescoping := by
  intro L d S k1 k2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.mul_sum, sum_deltaK]

end ThresholdHC.Proofs

