import ThresholdHC.BandCostSelection.Counting
import ThresholdHC.EntropyTailQuantile.CostEntropy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open scoped BigOperators Classical
namespace ThresholdHC.BandCostSelection

/-- Homogeneous cost entropy as a function of a multiset, including zero costs. -/
def multisetEntropy (a : Multiset ℝ) : ℝ :=
  a.sum + (a.map Real.negMulLog).sum - Real.negMulLog a.sum

theorem multisetEntropy_zero_cons (a : Multiset ℝ) :
    multisetEntropy (0 ::ₘ a) = multisetEntropy a := by
  simp [multisetEntropy]

/-- The multiset price is exactly the existing finite cost-entropy functional. -/
theorem multisetEntropy_ofFn {n : ℕ} (a : Fin n → ℝ) :
    multisetEntropy (↑(List.ofFn a)) = ThresholdHC.EntropyTailQuantile.costEntropy a := by
  simp [multisetEntropy, ThresholdHC.EntropyTailQuantile.costEntropy,
    ThresholdHC.EntropyTailQuantile.costTotal, List.map_ofFn, List.sum_ofFn]

theorem multisetEntropy_log_formula {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    multisetEntropy (↑(List.ofFn a)) =
      (∑ i, a i) + ∑ i, a i * Real.log ((∑ j, a j) / a i) := by
  rw [multisetEntropy_ofFn, ThresholdHC.EntropyTailQuantile.costEntropy_eq_log_sum ha]
  rfl

/-- A feasible minimizer of the entropy-tail finite-menu objective survives pruning.
The zero tag can represent the empty suffix because its entropy contribution vanishes. -/
theorem entropy_solve_attains {α κ : Type*} (tag : α → κ) (cost : κ → ℝ)
    (saving : α → ℝ) (menus : List (Finset α)) (hne : (enumerate menus).Nonempty)
    (ρ B ordinary : ℝ) :
    ∃ ys ∈ solve tag saving menus, ∀ xs ∈ enumerate menus,
      min ρ (Real.sqrt (ρ * multisetEntropy ((traceKey tag ys).map cost) / B) +
        ordinary - traceSaved saving ys) ≤
      min ρ (Real.sqrt (ρ * multisetEntropy ((traceKey tag xs).map cost) / B) +
        ordinary - traceSaved saving xs) :=
  solve_attains tag saving menus hne (fun k => Real.sqrt (ρ * multisetEntropy (k.map cost) / B))
    ordinary ρ

end ThresholdHC.BandCostSelection

