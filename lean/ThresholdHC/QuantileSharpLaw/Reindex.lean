import ThresholdHC.QuantileSharpLaw.FiniteMerge

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

def outwardCosts (n : ℕ) (a : ℕ → ℝ) : Option (Fin n) → ℝ
  | none => a n
  | some i => a i.rev.val

theorem outwardCosts_nonneg (n : ℕ) {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (i : Option (Fin n)) :
    0 ≤ outwardCosts n a i := by
  cases i with
  | none => exact ha n
  | some i => exact ha i.rev.val

theorem outwardCosts_sum (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ) :
    (∑ i, f (outwardCosts n a i)) = ∑ j : Fin (n+1), f (a j.val) := by
  rw [Fintype.sum_option,Fin.sum_univ_castSucc]
  simp only [outwardCosts,Fin.val_castSucc,Fin.val_last]
  have hs : (∑ i : Fin n, f (a i.rev.val)) = ∑ i : Fin n, f (a i.val) :=
    Fintype.sum_bijective Fin.rev Fin.rev_bijective _ _ (fun _ => rfl)
  rw [hs]
  ring

theorem outwardCosts_total (n : ℕ) (a : ℕ → ℝ) :
    costTotal (outwardCosts n a) = costTotal (fun i : Fin (n+1) => a i.val) :=
  outwardCosts_sum n a id

theorem outwardCosts_entropy (n : ℕ) (a : ℕ → ℝ) :
    costEntropy (outwardCosts n a) = costEntropy (fun i : Fin (n+1) => a i.val) := by
  unfold costEntropy
  rw [outwardCosts_total,outwardCosts_sum n a negMulLog]

theorem bumpedCost_entropy_rev {n : ℕ} (a y : ℝ) (v : Fin n → ℝ) :
    costEntropy (bumpedCost a (fun i : Fin n => v i.rev) y) = costEntropy (bumpedCost a v y) := by
  have hsum (f : Fin n → ℝ) : (∑ i : Fin n, f i.rev) = ∑ i, f i :=
    Fintype.sum_bijective Fin.rev Fin.rev_bijective _ _ (fun _ => rfl)
  rw [bumpedCost_entropy,bumpedCost_entropy]
  unfold costTotal
  rw [hsum v,hsum (fun i => negMulLog (v i))]

end ThresholdHC.QuantileSharpLaw
