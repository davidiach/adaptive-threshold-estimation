import ThresholdHC.QuantileOptimality.CoreMeasure
import ThresholdHC.QuantileOptimality.BlockEntropy

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile
open ThresholdHC.BandwiseSuffix (packet)

theorem coreGap_band_index {m n : ℕ} (hn : m+2 ≤ n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (j : Fin m) : coreGap hn η hη hη1 j ∈ band (n-(j.val+1)) := by
  have h := aboveGap_band (Fin.castLE (by omega : m ≤ n) j) hη hη1
  simpa only [coreGap,Fin.val_rev,Fin.val_castLE] using h

theorem realizingCore_entropy_lower {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ENNReal.ofReal (inverseScale n x*costEntropy x) ≤
      measureCostEntropy (realizingCore hn x η hη hη1) := by
  let k := n-m
  let C := realizingCore hn x η hη hη1
  let z := fun i : Fin (m+1) => inverseScale n x*packedCosts x i
  have hz : ∀ i, 0 ≤ z i := fun i => mul_nonneg (inverseScale_pos n hx).le (packedCosts_nonneg hx i)
  have hblock (i : Fin (m+1)) : z i ≤ bandCost C (k+i.val) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hindex : k+m=n := by dsimp [k]; omega
      simp only [z,packedCosts,Fin.lastCases_last,Fin.val_last,hindex]
      have hb := bandCost_mono (boundaryCore_le_realizingCore hn x hη hη1) n
      have hcost := packet_real_bandCost (mul_nonneg (inverseScale_pos n hx).le (hx none)) (edgeGap n) n
      rw [ite_eq_left (edgeGap_band n)] at hcost
      exact hcost.symm.le.trans hb
    · have hindex : n-(j.rev.val+1)=k+j.val := by simp only [Fin.val_rev]; dsimp [k]; omega
      simp only [z,packedCosts,Fin.lastCases_castSucc,Fin.val_castSucc]
      have hb := bandCost_mono (skipped_packet_le_realizingCore hn x hη hη1 j.rev) (k+j.val)
      have hcost := packet_real_bandCost (mul_nonneg (inverseScale_pos n hx).le (hx (some j.rev)))
        (coreGap hn η hη hη1 j.rev) (k+j.val)
      rw [ite_eq_left (by simpa only [hindex] using coreGap_band_index hn hη hη1 j.rev)] at hcost
      exact hcost.symm.le.trans hb
  have hcost := costEntropy_tail_block_le
    (fun i : Fin (k+(m+1)) => bandCost_nonneg C i.val) hz hblock
  have he : costEntropy z=inverseScale n x*costEntropy x := by
    rw [costEntropy_smul,packedCosts_entropy]
  rw [he] at hcost
  exact (ENNReal.ofReal_le_ofReal hcost).trans
    (le_iSup (fun N => ENNReal.ofReal (costEntropy (fun i : Fin N => bandCost C i.val))) (k+(m+1)))

theorem quantileCore_entropy_lower {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ENNReal.ofReal (inverseScale n x*costEntropy x) ≤
      measureCostEntropy (quantileCore (realizingLaw hn x η hη hη1) (chosenRarity m x)) := by
  rw [realizingLaw_quantileCore hn hx hη hη1]
  exact realizingCore_entropy_lower hn hx hη hη1

end ThresholdHC.QuantileOptimality
