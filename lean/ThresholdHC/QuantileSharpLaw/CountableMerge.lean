import ThresholdHC.QuantileSharpLaw.FiniteMerge
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open Real Filter
open scoped BigOperators Topology
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem summable_of_prefix_entropy_bound {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hC : ∀ n, costEntropy (fun i : Fin n => a i.val) ≤ C) :
    Summable a := by
  apply summable_of_sum_range_le ha
  intro n
  rw [← Fin.sum_univ_eq_sum_range a n]
  exact (costTotal_le_costEntropy (fun i : Fin n => ha i.val)).trans (hC n)

theorem merged_tail_entropy_le {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hC : ∀ n, costEntropy (fun i : Fin n => a i.val) ≤ C) (n : ℕ) :
    costEntropy (bumpedCost (∑' j : ℕ, a (n+j)) (fun i : Fin n => a i.val) 0) ≤ C := by
  have hs := (summable_of_prefix_entropy_bound ha hC).comp_injective
    (show Function.Injective (fun j : ℕ => n+j) from fun _ _ h => Nat.add_left_cancel h)
  have hc : Continuous (fun t : ℝ => costEntropy (bumpedCost t (fun i : Fin n => a i.val) 0)) := by
    apply continuous_costEntropy.comp
    apply continuous_pi
    intro i
    cases i with
    | none => change Continuous (fun t : ℝ => t+0^2); fun_prop
    | some i => exact continuous_const
  have hlim := hc.continuousAt.tendsto.comp hs.hasSum.tendsto_sum_nat
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro m
  have h := costEntropy_merge_tail (fun i : Fin (n+m) => a i.val) (fun i => ha i.val)
  have h' := h.trans (hC (n+m))
  simp only [Fin.val_natAdd,Fin.val_castAdd] at h'
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => a (n+j)) m] at h'
  simpa only [Function.comp_apply] using h'

end ThresholdHC.QuantileSharpLaw
