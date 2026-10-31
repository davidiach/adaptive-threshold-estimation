import ThresholdHC.EntropyTailAssembly.BandWeights

/-! Exact entropy cost of the normalized active-band bank. -/

noncomputable section
open MeasureTheory Real
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTail

theorem bandWeights_log (σ : Measure Gap) (j : ℕ) :
    log ((bandWeights σ j:ℝ)⁻¹) = log ((∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)/bandCost σ j) := by
  rw [bandWeights_coe, inv_div]

theorem bandWeights_entropy (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) :
    (∑ j : Fin N, bandCost σ j.val*(1+log ((bandWeights σ j.val:ℝ)⁻¹))) =
      costEntropy (fun j : Fin N => bandCost σ j.val) := by
  simp_rw [bandWeights_log, inverseSquare_eq_band_total σ hs hN]
  rw [costEntropy_eq_log_sum (fun j : Fin N => bandCost_nonneg σ j.val)]
  simp only [mul_add, mul_one, Finset.sum_add_distrib, costTotal]

theorem bandWeights_positive (σ : Measure Gap) {j : ℕ}
    (hA : 0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) (hj : 0 < bandCost σ j) :
    0 < (bandWeights σ j:ℝ) := by
  rw [bandWeights_coe]
  exact div_pos hj hA

theorem inverseSquare_zero_measure (σ : Measure Gap)
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ)
    (hz : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) = 0) : σ = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun d : Gap => sq_nonneg ((d:ℝ)⁻¹)) hσ).mp hz
  have hf : ∀ᵐ d : Gap ∂σ, False := by
    filter_upwards [hae] with d hd
    exact (sq_pos_of_pos (inv_pos.mpr d.property.1)).ne' hd
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hf

end ThresholdHC.EntropyTailAssembly
