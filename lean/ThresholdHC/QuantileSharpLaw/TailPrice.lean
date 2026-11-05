import ThresholdHC.QuantileSharpLaw.CoreReduction

noncomputable section
open Real
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem augmented_tail_absorption {ι : Type*} [Fintype ι] {v : Option ι → ℝ} {e M R : ℝ}
    (hv : ∀ i, 0 ≤ v i) (he : 0 ≤ e) (he1 : e ≤ 1) (hM : (1-e)^2 ≤ M)
    (hR : sqrt (costEntropy (fun i => v i+M*boundaryUnit i)) ≤ R) :
    sqrt (costEntropy (fun i => v i+boundaryUnit i)) ≤ e+R := by
  have h := skipped_tail_absorption (hv none) (fun i => hv (some i)) he he1
  have he1' : bumpedCost (v none) (fun i => v (some i)) 1 =
      (fun i => v i+boundaryUnit i) := by
    funext i
    cases i <;> simp [bumpedCost,boundaryUnit]
  rw [he1'] at h
  have hm : costEntropy (bumpedCost (v none) (fun i => v (some i)) (1-e)) ≤
      costEntropy (fun i => v i+M*boundaryUnit i) := by
    apply costEntropy_mono (bumpedCost_nonneg (hv none) (fun i => hv (some i)) (1-e))
    intro i
    cases i with
    | none =>
      change v none+(1-e)^2 ≤ v none+M*1
      simpa only [mul_one] using add_le_add le_rfl hM
    | some i =>
      change v (some i) ≤ v (some i)+M*0
      simp
  exact h.trans (add_le_add le_rfl ((sqrt_le_sqrt hm).trans hR))

theorem normalized_selection_price {n : ℕ} {v b : Option (Fin n) → ℝ} {e M R c : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hM : (1-e)^2 ≤ M) (hR : sqrt (costEntropy (fun i => v i+M*boundaryUnit i)) ≤ R)
    (hc : fullCoreCost n b ≤ c) :
    1+sqrt (costEntropy (fun i => v i+b i)) ≤ scalarRoot*(R+e+c) := by
  have h := core_vector_bound v b hv hb
  have ht := augmented_tail_absorption hv he he1 hM hR
  have hp : sqrt (costEntropy (fun i => v i+boundaryUnit i))+fullCoreCost n b ≤ R+e+c := by
    linarith only [ht,hc]
  exact h.trans (mul_le_mul_of_nonneg_left hp ((sqrt_nonneg 2).trans scalarRoot_spec.1.1))

end ThresholdHC.QuantileSharpLaw
