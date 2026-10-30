import ThresholdHC.EntropyTail.Model

/-! Elementary facts about the homogeneous cost entropy `G`. -/
noncomputable section
namespace ThresholdHC.EntropyTail

/-- `G(a) ≥ A` for nonnegative coordinates. -/
theorem sum_le_costEntropy {n : ℕ} (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∑ j, a j ≤ costEntropy a := by
  unfold costEntropy
  have : 0 ≤ ∑ j, a j * Real.log ((∑ i, a i) / a j) := by
    refine Finset.sum_nonneg fun j _ => ?_
    rcases (ha j).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · refine mul_nonneg (ha j) (Real.log_nonneg ?_)
      rw [le_div_iff₀ h, one_mul]
      exact Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j)
  linarith

/-- With at most one nonzero coordinate, `G(a) = A`. -/
theorem costEntropy_eq_sum {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i j, a i ≠ 0 → a j ≠ 0 → i = j) : costEntropy a = ∑ j, a j := by
  unfold costEntropy
  have : ∑ j, a j * Real.log ((∑ i, a i) / a j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : a j = 0
    · rw [hj, zero_mul]
    · have hs : ∑ i, a i = a j := by
        refine Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (Finset.mem_univ j) h)
        by_contra hi
        exact hij (ha i j hi hj)
      rw [hs, div_self hj, Real.log_one, mul_zero]
  rw [this, add_zero]

end ThresholdHC.EntropyTail
