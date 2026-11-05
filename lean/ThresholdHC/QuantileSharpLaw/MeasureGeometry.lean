import ThresholdHC.QuantileSharpLaw.CoreWork
import ThresholdHC.QuantileSharpLaw.MeasureMerge

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

theorem exists_boundary_band {t : ℝ} (ht : 0 < t) (htop : t ≤ 1/2) :
    ∃ n : ℕ, bandEdge (n+1) < t ∧ t ≤ bandEdge n := by
  obtain ⟨N,hN,hbefore⟩ := exists_band_cutoff ht
  cases N with
  | zero =>
    have h0 : t ≤ bandEdge 0 := by simpa [bandEdge] using htop
    exact False.elim ((not_lt_of_ge h0) hN)
  | succ n => exact ⟨n,hN,hbefore n (Nat.lt_succ_self n)⟩

theorem outward_measure_entropy (V : Measure Gap) {t : ℝ} (n : ℕ)
    (ht : bandEdge (n+1) < t) (hV : ∀ᵐ d : Gap ∂V, t ≤ (d : ℝ)) :
    (measureCostEntropy V).toReal = costEntropy (outwardCosts n (bandCost V)) := by
  rw [measureCostEntropy_eq_prefix_of_support V hV ht,
    ENNReal.toReal_ofReal (costEntropy_nonneg (fun i : Fin (n+1) => bandCost_nonneg V i.val))]
  exact (outwardCosts_entropy n (bandCost V)).symm

theorem outwardCosts_add (n : ℕ) (a b : ℕ → ℝ) :
    outwardCosts n (fun j => a j+b j) = (fun i => outwardCosts n a i+outwardCosts n b i) := by
  funext i
  cases i <;> rfl

theorem merged_measure_entropy (L V : Measure Gap) [IsFiniteMeasure L] [IsFiniteMeasure V]
    (hLV : measureCostEntropy (L+V) ≠ ⊤) {t : ℝ} (n : ℕ)
    (htlow : bandEdge (n+1) < t) (hthigh : t ≤ bandEdge n)
    (hL : ∀ᵐ d : Gap ∂L, (d : ℝ) ≤ t) (hV : ∀ᵐ d : Gap ∂V, t ≤ (d : ℝ)) :
    costEntropy (fun i => outwardCosts n (bandCost V) i+
      (∑' j, bandCost L j)*boundaryUnit i) ≤ (measureCostEntropy (L+V)).toReal := by
  have he : (fun i => outwardCosts n (bandCost V) i+(∑' j, bandCost L j)*boundaryUnit i) =
      bumpedCost (bandCost V n+∑' j, bandCost L j) (fun i : Fin n => bandCost V i.rev.val) 0 := by
    funext i
    cases i <;> simp [outwardCosts,boundaryUnit,bumpedCost]
  rw [he]
  exact selected_measure_merge L V hLV n htlow hthigh hL hV

end ThresholdHC.QuantileSharpLaw
