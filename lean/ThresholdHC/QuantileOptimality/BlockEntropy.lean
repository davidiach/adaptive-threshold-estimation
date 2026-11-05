import ThresholdHC.QuantileOptimality.Specification
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.EntropyTailQuantile

def packedCosts {m : ℕ} (x : Option (Fin m) → ℝ) : Fin (m+1) → ℝ :=
  Fin.lastCases (x none) (fun i : Fin m => x (some i.rev))

theorem packedCosts_sum {m : ℕ} (x : Option (Fin m) → ℝ) (f : ℝ → ℝ) :
    (∑ i, f (packedCosts x i)) = ∑ i, f (x i) := by
  rw [Fin.sum_univ_castSucc,Fintype.sum_option]
  simp only [packedCosts,Fin.lastCases_last,Fin.lastCases_castSucc]
  have hs : (∑ i : Fin m, f (x (some i.rev))) = ∑ i : Fin m, f (x (some i)) :=
    Fintype.sum_bijective Fin.rev Fin.rev_bijective _ _ (fun _ => rfl)
  rw [hs]
  ring

theorem packedCosts_entropy {m : ℕ} (x : Option (Fin m) → ℝ) :
    costEntropy (packedCosts x)=costEntropy x := by
  have ht : costTotal (packedCosts x)=costTotal x := packedCosts_sum x id
  unfold costEntropy
  rw [ht,packedCosts_sum x negMulLog]

theorem packedCosts_nonneg {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    (i : Fin (m+1)) : 0 ≤ packedCosts x i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [packedCosts,Fin.lastCases_last] using hx none
  · simpa only [packedCosts,Fin.lastCases_castSucc] using hx (some j.rev)

theorem costEntropy_zero_append {k m : ℕ} (v : Fin m → ℝ) :
    costEntropy (Fin.append (0 : Fin k → ℝ) v)=costEntropy v := by
  unfold costEntropy costTotal
  simp only [Fin.sum_univ_add,Fin.append_left,Fin.append_right,Pi.zero_apply,
    negMulLog_zero,Finset.sum_const_zero,zero_add]

theorem costEntropy_tail_block_le {k m : ℕ} {a : Fin (k+m) → ℝ} {v : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, 0 ≤ v i) (hblock : ∀ i, v i ≤ a (Fin.natAdd k i)) :
    costEntropy v ≤ costEntropy a := by
  rw [← costEntropy_zero_append (k := k) v]
  apply costEntropy_mono
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left,Pi.zero_apply,le_refl]
    · simpa only [Fin.append_right] using hv j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,Pi.zero_apply] using ha (Fin.castAdd m j)
    · simpa only [Fin.append_right] using hblock j

end ThresholdHC.QuantileOptimality
