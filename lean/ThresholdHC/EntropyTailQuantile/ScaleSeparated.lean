import ThresholdHC.EntropyTailQuantile.BandGeometry
import ThresholdHC.EntropyTailQuantile.TailModulus

/-! The scale-separated bound Γ(ξ) ≤ 4 H(ξ)/t for a measure on [t, 1/2]. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

theorem bandCost_eq_zero_of_support (σ : Measure Gap) {t : ℝ} {j : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hj : bandEdge j < t) : bandCost σ j = 0 := by
  have hm : σ (band j) = 0 := by
    apply measure_mono_null (t := {d : Gap | (d:ℝ) < t})
    · intro d hd
      exact hd.2.trans_lt hj
    · simpa only [ae_iff, not_le] using hs
  simp only [bandCost, Measure.restrict_eq_zero.mpr hm, integral_zero_measure]

theorem measureCostEntropy_eq_prefix_of_support (σ : Measure Gap) {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) :
    measureCostEntropy σ = ENNReal.ofReal (costEntropy (fun i : Fin N => bandCost σ i)) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply costEntropy_prefix_le_of_eventually_zero (bandCost_nonneg σ)
    intro j hj
    exact bandCost_eq_zero_of_support σ hs ((bandEdge_antitone hj).trans_lt hN)
  · exact le_iSup (fun n => ENNReal.ofReal (costEntropy (fun i : Fin n => bandCost σ i))) N

theorem scaleSeparated_entropy (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ}
    (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) :
    measureCostEntropy σ ≤ ENNReal.ofReal ((4/t) * ∫ d : Gap, (d:ℝ)⁻¹ ∂σ) := by
  obtain ⟨N, hN, hbefore⟩ := exists_band_cutoff ht
  rw [measureCostEntropy_eq_prefix_of_support σ hs hN]
  apply ENNReal.ofReal_le_ofReal
  have hH := inverse_integrable_of_support σ ht hs
  have href := @costEntropy_le_reference (Fin N) _
    (fun i => bandCost σ i) (fun i => t * (2:ℝ)^(i:ℕ))
    (fun i => bandCost_nonneg σ i) (fun i => by positivity)
    (dyadic_reference_sum_le_one ht.le hbefore)
  apply href.trans
  have hband (j : Fin N) : bandCost σ j * (1-log (t * (2:ℝ)^(j:ℕ))) ≤
      (4/t) * ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂σ := by
    rw [bandCost, ← integral_mul_const, ← integral_const_mul]
    apply integral_mono_ae ((band_inverseSquare_integrable σ j).mul_const _)
      (hH.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem (measurableSet_band j)] with d hd
    calc
      (d:ℝ)⁻¹^2 * (1-log (t * (2:ℝ)^(j:ℕ))) ≤
          (d:ℝ)⁻¹^2 * ((4/t) * (d:ℝ)) :=
        mul_le_mul_of_nonneg_left (dyadic_reference_coefficient ht j d hd) (sq_nonneg _)
      _ = (4/t) * (d:ℝ)⁻¹ := by field_simp
  calc
    _ ≤ ∑ j : Fin N, (4/t) * ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂σ :=
      Finset.sum_le_sum (fun j _ => hband j)
    _ = (4/t) * ∑ j : Fin N, ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂σ := by
      rw [Finset.mul_sum]
    _ ≤ (4/t) * ∫ d : Gap, (d:ℝ)⁻¹ ∂σ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← integral_iUnion_fintype (fun j : Fin N => measurableSet_band j)
        (fun i j hij => bands_disjoint (Fin.val_ne_iff.mpr hij))
        (fun _ => hH.integrableOn)]
      exact setIntegral_le_integral hH
        (Filter.Eventually.of_forall (fun d : Gap => inv_nonneg.mpr d.property.1.le))

end ThresholdHC.EntropyTailQuantile
