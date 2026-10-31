import ThresholdHC.EntropyTailQuantile.CostEntropy

/-! Increasing prefixes of the countable homogeneous cost entropy. -/

noncomputable section
open Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailQuantile

theorem costEntropy_prefix_succ {a : ℕ → ℝ} (n : ℕ) :
    costEntropy (fun i : Fin (n+1) => a i) =
      costEntropy (fun i : Fin n => a i) + a n +
        negMulLog (a n) + negMulLog (costTotal (fun i : Fin n => a i)) -
        negMulLog (costTotal (fun i : Fin n => a i) + a n) := by
  simp only [costEntropy, costTotal, Fin.sum_univ_castSucc, Fin.val_castSucc,
    Fin.val_last]
  ring

theorem costEntropy_prefix_monotone {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Monotone (fun n => costEntropy (fun i : Fin n => a i)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [costEntropy_prefix_succ]
  have h := negMulLog_add_le (costTotal_nonneg (fun i : Fin n => ha i)) (ha n)
  linarith [ha n]

theorem costEntropy_prefix_eq_of_eventually_zero {a : ℕ → ℝ} {N n : ℕ}
    (hz : ∀ j, N ≤ j → a j = 0) (hn : N ≤ n) :
    costEntropy (fun i : Fin n => a i) = costEntropy (fun i : Fin N => a i) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [costEntropy_prefix_succ, hz n hn]; simpa using ih

theorem costEntropy_prefix_le_of_eventually_zero {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ i, 0 ≤ a i) (hz : ∀ j, N ≤ j → a j = 0) (n : ℕ) :
    costEntropy (fun i : Fin n => a i) ≤ costEntropy (fun i : Fin N => a i) := by
  rcases le_total n N with hn | hn
  · exact costEntropy_prefix_monotone ha hn
  · exact (costEntropy_prefix_eq_of_eventually_zero hz hn).le

end ThresholdHC.EntropyTailQuantile
