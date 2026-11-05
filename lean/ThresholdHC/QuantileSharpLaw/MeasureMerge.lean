import ThresholdHC.QuantileSharpLaw.MomentSeries
import ThresholdHC.QuantileSharpLaw.SeriesSplit

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

theorem tail_bandCost_zero (L : Measure Gap) {t : ℝ} {n j : ℕ}
    (hL : ∀ᵐ d : Gap ∂L, (d : ℝ) ≤ t) (ht : t ≤ bandEdge n) (hj : j < n) :
    bandCost L j=0 := by
  have hcut : t ≤ bandEdge j/2 := by
    rw [← bandEdge_succ]
    exact ht.trans (bandEdge_antitone (Nat.succ_le_of_lt hj))
  have hnull : L {d : Gap | t < (d : ℝ)}=0 := by
    simpa only [ae_iff,not_le] using hL
  have hband : L (band j)=0 := measure_mono_null
    (fun d hd => hcut.trans_lt hd.1) hnull
  simp only [bandCost,Measure.restrict_eq_zero.mpr hband,integral_zero_measure]

theorem selected_measure_merge (L V : Measure Gap) [IsFiniteMeasure L] [IsFiniteMeasure V]
    (hLV : measureCostEntropy (L+V) ≠ ⊤) {t : ℝ} (n : ℕ)
    (htlow : bandEdge (n+1) < t) (hthigh : t ≤ bandEdge n)
    (hL : ∀ᵐ d : Gap ∂L, (d : ℝ) ≤ t) (hV : ∀ᵐ d : Gap ∂V, t ≤ (d : ℝ)) :
    costEntropy (bumpedCost (bandCost V n+∑' j, bandCost L j)
      (fun i : Fin n => bandCost V i.rev.val) 0) ≤ (measureCostEntropy (L+V)).toReal := by
  apply selected_tail_merge (a := bandCost (L+V)) n (bandCost_nonneg V) (bandCost_nonneg L)
  · intro j
    rw [bandCost_add]
    ring
  · intro j hj
    exact bandCost_eq_zero_of_support V hV
      ((bandEdge_antitone (Nat.succ_le_of_lt hj)).trans_lt htlow)
  · intro j hj
    exact tail_bandCost_zero L hL hthigh hj
  · exact measure_prefix_entropy_bound (L+V) hLV

end ThresholdHC.QuantileSharpLaw
