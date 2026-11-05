import ThresholdHC.QuantileSharpLaw.CoreIdentities

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem costEntropy_merge_tail {n m : ℕ} (a : Fin (n+m) → ℝ) (ha : ∀ i, 0 ≤ a i) :
    costEntropy (bumpedCost (∑ j : Fin m, a (Fin.natAdd n j))
      (fun i : Fin n => a (Fin.castAdd m i)) 0) ≤ costEntropy a := by
  have hs := negMulLog_sum_le (fun j : Fin m => a (Fin.natAdd n j))
    (fun j => ha (Fin.natAdd n j))
  rw [bumpedCost_entropy]
  simp only [pow_two,zero_mul,add_zero]
  unfold costEntropy costTotal at *
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  dsimp only at hs ⊢
  rw [add_comm (∑ j : Fin m, a (Fin.natAdd n j)) (∑ i : Fin n, a (Fin.castAdd m i))]
  linarith only [hs]

theorem costEntropy_reverse {n : ℕ} (a : Fin n → ℝ) :
    costEntropy (fun i : Fin n => a i.rev) = costEntropy a := by
  have hsum (f : Fin n → ℝ) : (∑ i : Fin n, f i.rev) = ∑ i, f i :=
    Fintype.sum_bijective Fin.rev Fin.rev_bijective _ _ (fun _ => rfl)
  unfold costEntropy costTotal
  rw [hsum a,hsum (fun i => negMulLog (a i))]

end ThresholdHC.QuantileSharpLaw
