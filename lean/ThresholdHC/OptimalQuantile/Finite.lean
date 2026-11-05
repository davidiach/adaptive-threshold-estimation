import ThresholdHC.OptimalQuantile.FiniteModel

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.OptimalQuantile
open ThresholdHC.EntropyTailQuantile

/-- Exact finite-vector reduction to a one-dimensional family of exponential
partition inequalities. The measure-to-vector reduction remains a separate step. -/
theorem finiteVectorBound_iff_partition (n : ℕ) {k : ℝ} (hk : 1 ≤ k) :
    finiteVectorBound n k ↔ ∀ u : ℝ, 1 ≤ u → finitePartition n k u ≤ 1 := by
  have hk0 : 0 < k := by linarith
  constructor
  · intro h u hu
    rw [finitePartition_eq_sum]
    apply (root_price_iff_partition (tangentWeight (n := n) u)
      (tangentWeight_pos (by linarith : 0 < u)) hk0 (tangentOffset_nonneg hk hu)).mp
    intro x hx
    have ht := (price_iff_all_tangents (hx none) hk0.le).mp (h x hx) u hu
    rw [tangent_price_identity] at ht
    linarith
  · intro h x hx
    apply (price_iff_all_tangents (hx none) hk0.le).mpr
    intro u hu
    have hp := h u hu
    rw [finitePartition_eq_sum] at hp
    have ht := (root_price_iff_partition (tangentWeight (n := n) u)
      (tangentWeight_pos (by linarith : 0 < u)) hk0 (tangentOffset_nonneg hk hu)).mpr hp x hx
    rw [tangent_price_identity]
    linarith

end ThresholdHC.OptimalQuantile
