import ThresholdHC.QuantileSelection.Interaction
import ThresholdHC.EntropyTailQuantile.EntropyMixture
import ThresholdHC.EntropyTailQuantile.ScaleSeparated

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.QuantileSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

/-- Use the same increasing prefix for both costs, even when the supremum is infinite. -/
theorem entropy_superadditive (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] :
    measureCostEntropy σ + measureCostEntropy τ ≤ measureCostEntropy (σ+τ) := by
  have hm (ξ : Measure Gap) : Monotone (fun n => ENNReal.ofReal
      (costEntropy (fun i : Fin n => bandCost ξ i))) :=
    fun _ _ h => ENNReal.ofReal_le_ofReal (costEntropy_prefix_monotone (bandCost_nonneg ξ) h)
  unfold measureCostEntropy
  rw [ENNReal.iSup_add_iSup_of_monotone (hm σ) (hm τ)]
  apply iSup_mono
  intro n
  rw [← ENNReal.ofReal_add (costEntropy_nonneg (fun i : Fin n => bandCost_nonneg σ i))
    (costEntropy_nonneg (fun i : Fin n => bandCost_nonneg τ i))]
  simp only [bandCost_add]
  exact ENNReal.ofReal_le_ofReal (costEntropy_superadditive
    (fun i : Fin n => bandCost_nonneg σ i) (fun i => bandCost_nonneg τ i))

/-- On a common separated support all three entropies equal the same finite prefix. -/
theorem core_interaction (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {t : ℝ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (htau : ∀ᵐ d : Gap ∂τ, t ≤ (d:ℝ)) :
    (measureCostEntropy (σ+τ)).toReal ≤ (measureCostEntropy σ).toReal + (measureCostEntropy τ).toReal +
      sqrt (2 * (measureCostEntropy σ).toReal * (measureCostEntropy τ).toReal) := by
  obtain ⟨N, hN, _⟩ := exists_band_cutoff ht
  have hboth : ∀ᵐ d : Gap ∂(σ+τ), t ≤ (d:ℝ) := ae_add_measure_iff.mpr ⟨hs, htau⟩
  rw [measureCostEntropy_eq_prefix_of_support _ hboth hN, measureCostEntropy_eq_prefix_of_support _ hs hN,
    measureCostEntropy_eq_prefix_of_support _ htau hN]
  simp only [ENNReal.toReal_ofReal (costEntropy_nonneg (fun i : Fin N => bandCost_nonneg _ i)),
    bandCost_add]
  obtain ⟨h₁,h₂⟩ := entropy_interaction (fun i : Fin N => bandCost σ i) (fun i : Fin N => bandCost τ i)
    (fun i => bandCost_nonneg _ i) (fun i => bandCost_nonneg _ i)
  rw [ENNReal.toReal_ofReal (costEntropy_nonneg (fun i : Fin N => add_nonneg (bandCost_nonneg σ i) (bandCost_nonneg τ i)))]
  exact h₁.trans h₂

end ThresholdHC.QuantileSelection
