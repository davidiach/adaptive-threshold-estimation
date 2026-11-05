import ThresholdHC.OptimalQuantile.Root

noncomputable section
open Real
namespace ThresholdHC.OptimalQuantile
open ThresholdHC.EntropyTailQuantile

theorem finiteVectorBound_zero_requires_sqrt_two {k : ℝ} (hk : finiteVectorBound 0 k) :
    sqrt 2 ≤ k := by
  have h := hk (fun _ => 1) (by intro i; norm_num)
  norm_num [costEntropy,costTotal,dyadicCost] at h
  have hs : (sqrt (2 : ℝ))^2 = 2 := sq_sqrt (by norm_num)
  apply (mul_le_mul_iff_left₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mp
  nlinarith only [hs,h]

theorem all_finite_bounds_iff_root_unrestricted (k : ℝ) :
    (∀ n : ℕ, finiteVectorBound n k) ↔ scalarRoot ≤ k := by
  constructor
  · intro h
    exact (all_finite_bounds_iff_root (finiteVectorBound_zero_requires_sqrt_two (h 0))).mp h
  · intro h
    exact (all_finite_bounds_iff_root (scalarRoot_spec.1.1.trans h)).mpr h

theorem finite_vector_witness_below_root {k : ℝ} (hk : k < scalarRoot) :
    ∃ n : ℕ, ∃ x : Option (Fin n) → ℝ, (∀ i, 0 ≤ x i) ∧
      k*(sqrt (1+x none)+dyadicCost n x) < 1+sqrt (costEntropy x) := by
  classical
  have hn : ¬ ∀ n : ℕ, finiteVectorBound n k := by
    intro h
    exact (not_le_of_gt hk) ((all_finite_bounds_iff_root_unrestricted k).mp h)
  simpa only [finiteVectorBound,not_forall,not_imp,not_le,exists_prop] using hn

end ThresholdHC.OptimalQuantile
