import ThresholdHC.QuantileSelection.ScaleWeights
import ThresholdHC.QuantileSelection.Specification
import ThresholdHC.EntropyTailQuantile.ScaleSeparated

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantileSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

/-- Lemma 2. Only the bands that meet the support enter the entropy. -/
theorem separated_cost : SeparatedCostStatement := by
  intro ξ _ t ht hs
  obtain ⟨N, hN, hbefore⟩ := exists_band_cutoff ht
  rw [measureCostEntropy_eq_prefix_of_support ξ hs hN]
  apply ENNReal.ofReal_le_ofReal
  have hw : ∑ j : Fin N, scaleWeight j.rev.val ≤ 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i : Fin N => scaleWeight i.val)).le.trans (scaleWeight_mass N)
  have hH := inverse_integrable_of_support ξ ht hs
  apply (costEntropy_le_reference (fun j : Fin N => bandCost_nonneg ξ j)
    (fun j => scaleWeight_pos j.rev.val) hw).trans
  have hband (j : Fin N) : bandCost ξ j * (1-log (scaleWeight j.rev.val)) ≤
      (2/t) * ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂ξ := by
    rw [bandCost, ← integral_mul_const, ← integral_const_mul]
    apply integral_mono_ae ((band_inverseSquare_integrable ξ j).mul_const _)
      (hH.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem (measurableSet_band j), ae_restrict_of_ae hs] with d hd hd'
    calc
      _ ≤ (d:ℝ)⁻¹^2 * ((2/t) * (d:ℝ)) :=
        mul_le_mul_of_nonneg_left (scaleWeight_band ht hbefore j d hd hd') (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j : Fin N, (2/t) * ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂ξ :=
      Finset.sum_le_sum (fun j _ => hband j)
    _ = (2/t) * ∑ j : Fin N, ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂ξ := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← integral_iUnion_fintype (fun j : Fin N => measurableSet_band j)
        (fun i j hij => bands_disjoint (Fin.val_ne_iff.mpr hij))
        (fun _ => hH.integrableOn)]
      exact setIntegral_le_integral hH
        (Filter.Eventually.of_forall (fun d : Gap => inv_nonneg.mpr d.property.1.le))

end ThresholdHC.QuantileSelection
