import ThresholdHC.QuantileSharpLaw.CountableMerge
import ThresholdHC.QuantileSharpLaw.Reindex

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem tail_sum_after_zeros {l : ℕ → ℝ} (hl : Summable l) (n : ℕ)
    (hz : ∀ j < n, l j=0) : (∑' j : ℕ, l (n+j)) = ∑' j, l j := by
  have h := hl.sum_add_tsum_nat_add n
  have hs : (∑ j ∈ Finset.range n, l j)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (Finset.mem_range.mp hj)
  rw [hs,zero_add] at h
  simpa only [Nat.add_comm] using h

theorem tail_sum_split {a v l : ℕ → ℝ} (hl : Summable l) (n : ℕ)
    (hsum : ∀ j, a j=v j+l j) (hv : ∀ j, n < j → v j=0) (hz : ∀ j < n, l j=0) :
    (∑' j : ℕ, a (n+j)) = v n+∑' j, l j := by
  have htail := hl.comp_injective
    (show Function.Injective (fun j : ℕ => n+j) from fun _ _ h => Nat.add_left_cancel h)
  have he : (fun j : ℕ => a (n+j)) =
      (fun j : ℕ => (if j=0 then v n else 0)+l (n+j)) := by
    funext j
    by_cases hj : j=0
    · subst j
      simp only [Nat.add_zero,hsum,ite_true]
    · rw [hsum,hv _ (by omega)]
      simp only [hj,ite_false,zero_add]
  have h := ((hasSum_ite_eq (0 : ℕ) (v n)).add htail.hasSum).tsum_eq
  change (∑' j : ℕ, ((if j=0 then v n else 0)+l (n+j))) = v n+(∑' j : ℕ, l (n+j)) at h
  rw [← he,tail_sum_after_zeros hl n hz] at h
  exact h

theorem selected_tail_merge {a v l : ℕ → ℝ} {C : ℝ} (n : ℕ)
    (hv : ∀ j, 0 ≤ v j) (hl : ∀ j, 0 ≤ l j) (hsum : ∀ j, a j=v j+l j)
    (hV : ∀ j, n < j → v j=0) (hL : ∀ j < n, l j=0)
    (hC : ∀ m, costEntropy (fun i : Fin m => a i.val) ≤ C) :
    costEntropy (bumpedCost (v n+∑' j, l j) (fun i : Fin n => v i.rev.val) 0) ≤ C := by
  have ha (j) : 0 ≤ a j := by rw [hsum]; exact add_nonneg (hv j) (hl j)
  have hlS : Summable l := Summable.of_nonneg_of_le hl
    (fun j => by rw [hsum]; exact le_add_of_nonneg_left (hv j))
    (summable_of_prefix_entropy_bound ha hC)
  have h := merged_tail_entropy_le ha hC n
  rw [tail_sum_split hlS n hsum hV hL] at h
  have hfirst : (fun i : Fin n => a i.val) = (fun i : Fin n => v i.val) := by
    funext i
    rw [hsum,hL i.val i.isLt,add_zero]
  rw [hfirst] at h
  rw [bumpedCost_entropy_rev (v n+∑' j, l j) 0 (fun i : Fin n => v i.val)]
  exact h

end ThresholdHC.QuantileSharpLaw
