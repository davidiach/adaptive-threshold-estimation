import ThresholdHC.BandCostSelection.Entropy
import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTailQuantile.ScaleSeparated

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.GapLawMenus
open ThresholdHC.Tier6 ThresholdHC.BandCostSelection

theorem list_entropy_prefix (a : ℕ → ℝ) (js : List ℕ) (hj : js.Nodup)
    (hz : ∀ j, j ∉ js → a j = 0) {N : ℕ} (hN : ∀ j ∈ js, j < N) :
    multisetEntropy (↑(js.map a)) =
      ThresholdHC.EntropyTailQuantile.costEntropy (fun j : Fin N => a j.val) := by
  have hs (f : ℕ → ℝ) (hf : ∀ j, j ∉ js → f j = 0) :
      (js.map f).sum = ∑ j : Fin N, f j.val := by
    rw [← List.sum_toFinset f hj,Fin.sum_univ_eq_sum_range]
    apply Finset.sum_subset
    · intro j hj'
      exact Finset.mem_range.mpr (hN j (List.mem_toFinset.mp hj'))
    · intro j _ hj'
      exact hf j (fun h => hj' (List.mem_toFinset.mpr h))
  have hs' := hs (fun j => Real.negMulLog (a j))
    (fun j h => by rw [hz j h,Real.negMulLog_zero])
  simp only [multisetEntropy,Multiset.map_coe,Multiset.sum_coe,List.map_map,Function.comp_def]
  rw [hs a hz,hs']
  rfl

/-- Finite occupied-band entropy agrees exactly with the original extended
prefix-supremum entropy; missing bands contribute zero. -/
theorem gamma_list (σ : Measure Gap) [IsFiniteMeasure σ]
    (js : List ℕ) (hj : js.Nodup)
    (hz : ∀ j, j ∉ js → ThresholdHC.EntropyTail.bandCost σ j = 0) :
    ThresholdHC.EntropyTail.gamma σ =
      ENNReal.ofReal (multisetEntropy
        (↑(js.map fun j => (ThresholdHC.EntropyTail.bandCost σ j).toReal))) := by
  let a := fun j => ThresholdHC.EntropyTailQuantile.bandCost σ j
  have ha : ∀ j, 0 ≤ a j := ThresholdHC.EntropyTailQuantile.bandCost_nonneg σ
  have haz : ∀ j, j ∉ js → a j = 0 := by
    intro j hj'
    dsimp [a]
    rw [ThresholdHC.EntropyTail.quantile_bandCost_eq,hz j hj']
    rfl
  let N := js.toFinset.sup id + 1
  have hN : ∀ j ∈ js, j < N := by
    intro j hj'
    have h : j ≤ js.toFinset.sup id := Finset.le_sup (f := id) (List.mem_toFinset.mpr hj')
    dsimp [N]
    omega
  have he : ThresholdHC.EntropyTailQuantile.measureCostEntropy σ =
      ENNReal.ofReal (ThresholdHC.EntropyTailQuantile.costEntropy (fun j : Fin N => a j.val)) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      apply ENNReal.ofReal_le_ofReal
      apply ThresholdHC.EntropyTailQuantile.costEntropy_prefix_le_of_eventually_zero ha
      intro j hNj
      apply haz j
      intro hj'
      have h := hN j hj'
      omega
    · exact le_iSup (fun n => ENNReal.ofReal
        (ThresholdHC.EntropyTailQuantile.costEntropy (fun j : Fin n => a j.val))) N
  rw [le_antisymm (ThresholdHC.EntropyTail.gamma_le_quantile_measureCostEntropy σ)
    (ThresholdHC.EntropyTail.quantile_measureCostEntropy_le σ),he,
    ← list_entropy_prefix a js hj haz hN]
  congr 1
  simp only [a,ThresholdHC.EntropyTail.quantile_bandCost_eq]

end ThresholdHC.GapLawMenus

