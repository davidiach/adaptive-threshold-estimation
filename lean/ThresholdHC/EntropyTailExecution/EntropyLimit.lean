import ThresholdHC.EntropyTailExecution.ThreePiece

/-! Remove the positive support cutoff by finite-band approximation. Only
entropy monotonicity and vanishing discarded inverse moment are required. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.EntropyTailAssembly ThresholdHC.RareAboveTwo

theorem finite_entropy_three_piece (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    (hΓ : measureCostEntropy σ < ⊤) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤ ENNReal.ofReal (128*ζ.real univ+
      28000*(sqrt (ρ*(measureCostEntropy σ).toReal)+(∫ d : Gap, (d:ℝ)⁻¹ ∂τ))/sqrt B) := by
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  let G := sqrt (ρ*(measureCostEntropy σ).toReal)
  have hrem (n : ℕ) : Integrable (fun d : Gap => (d:ℝ)⁻¹) (selectedRemainder σ n) :=
    (inverse_integrable_of_entropy σ hΓ).mono_measure (selectedRemainder_le σ n)
  have hbound (n : ℕ) : rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal (128*ζ.real univ+28000*(G+(H+
        (∫ d : Gap, (d:ℝ)⁻¹ ∂selectedRemainder σ n)))/sqrt B) := by
    have he : selectedTruncation σ n+(τ+selectedRemainder σ n)+ζ = σ+τ+ζ := by
      rw [show selectedTruncation σ n+(τ+selectedRemainder σ n)+ζ =
        (selectedTruncation σ n+selectedRemainder σ n)+τ+ζ by ac_rfl,
        selectedTruncation_add_remainder]
    let : IsProbabilityMeasure (selectedTruncation σ n+(τ+selectedRemainder σ n)+ζ) := by
      rw [he]; infer_instance
    have hN : bandEdge (n+1) < bandEdge n := by rw [bandEdge_succ]; linarith [bandEdge_pos n]
    have h := finite_support_three_piece (selectedTruncation σ n) (τ+selectedRemainder σ n) ζ
      (bandEdge_pos n) (selectedTruncation_support σ n) hN (hτ.add_measure (hrem n)) hρ hρ1 hB
    simp only [he, integral_add_measure hτ (hrem n)] at h
    have hg : costEntropy (fun j : Fin (n+1) => bandCost (selectedTruncation σ n) j.val) ≤
        (measureCostEntropy σ).toReal := by
      have hn := costEntropy_nonneg (fun j : Fin (n+1) => bandCost_nonneg (selectedTruncation σ n) j.val)
      rw [← ENNReal.toReal_ofReal hn]
      exact ENNReal.toReal_mono hΓ.ne ((le_iSup (fun k : ℕ => ENNReal.ofReal
        (costEntropy (fun j : Fin k => bandCost (selectedTruncation σ n) j.val))) (n+1)).trans
          (selectedTruncation_entropy_le σ n))
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    apply add_le_add (le_refl _)
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg B)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hg hρ.le)) (le_refl _)
  have hl := ENNReal.tendsto_ofReal
    (((((selectedRemainder_inverse_tendsto σ hΓ).const_add H).const_add G).const_mul 28000).div_const
      (sqrt B) |>.const_add (128*ζ.real univ))
  have hl' : Tendsto (fun n => ENNReal.ofReal (128*ζ.real univ+28000*(G+(H+
      (∫ d : Gap, (d:ℝ)⁻¹ ∂selectedRemainder σ n)))/sqrt B)) atTop
      (𝓝 (ENNReal.ofReal (128*ζ.real univ+28000*(G+H)/sqrt B))) := by
    simpa only [add_zero] using hl
  exact ge_of_tendsto hl' (Eventually.of_forall hbound)

end ThresholdHC.EntropyTailExecution
