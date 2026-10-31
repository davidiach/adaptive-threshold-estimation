import ThresholdHC.EntropyTailQuantile.MeasureEntropy

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

theorem bandCost_add (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] (j : ℕ) :
    bandCost (σ+τ) j = bandCost σ j + bandCost τ j := by
  unfold bandCost
  rw [Measure.restrict_add]
  exact integral_add_measure (band_inverseSquare_integrable σ j)
    (band_inverseSquare_integrable τ j)

theorem measureCostEntropy_add_le_two (σ τ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] :
    measureCostEntropy (σ+τ) ≤ 2 * measureCostEntropy σ + 2 * measureCostEntropy τ := by
  apply iSup_le
  intro n
  simp only [bandCost_add]
  calc
    _ ≤ ENNReal.ofReal (2 * costEntropy (fun i : Fin n => bandCost σ i) +
        2 * costEntropy (fun i : Fin n => bandCost τ i)) :=
      ENNReal.ofReal_le_ofReal (costEntropy_add_le_two
        (fun i : Fin n => bandCost_nonneg σ i) (fun i => bandCost_nonneg τ i))
    _ = 2 * ENNReal.ofReal (costEntropy (fun i : Fin n => bandCost σ i)) +
        2 * ENNReal.ofReal (costEntropy (fun i : Fin n => bandCost τ i)) := by
      rw [ENNReal.ofReal_add (by positivity [costEntropy_nonneg (fun i : Fin n => bandCost_nonneg σ i)])
        (by positivity [costEntropy_nonneg (fun i : Fin n => bandCost_nonneg τ i)])]
      simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ _ := add_le_add
      (mul_le_mul_right (le_iSup (fun k => ENNReal.ofReal
        (costEntropy (fun i : Fin k => bandCost σ i))) n) (2 : ℝ≥0∞))
      (mul_le_mul_right (le_iSup (fun k => ENNReal.ofReal
        (costEntropy (fun i : Fin k => bandCost τ i))) n) (2 : ℝ≥0∞))

end ThresholdHC.EntropyTailQuantile
