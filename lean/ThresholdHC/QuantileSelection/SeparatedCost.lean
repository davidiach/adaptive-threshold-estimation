import ThresholdHC.QuantileSelection.ScaleWeights
import ThresholdHC.QuantileSelection.Specification
import ThresholdHC.EntropyTailQuantile.ScaleSeparated

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantileSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

/-- A positive subprobability reference on the occupied bands gives a
separated inverse-moment estimate with its pointwise coefficient. -/
theorem separated_cost_of_weights (K : ℝ) (hK : 0 ≤ K) (w : ℕ → ℝ)
    (hpos : ∀ n, 0 < w n) (hmass : ∀ N, ∑ i : Fin N, w i.val ≤ 1)
    (hcoeff : ∀ {N : ℕ} {t : ℝ}, 0 < t → (∀ j < N, t ≤ bandEdge j) →
      ∀ (j : Fin N) (d : Gap), d ∈ band j → t ≤ (d:ℝ) → 1-log (w j.rev.val) ≤ (K/t)*(d:ℝ))
    (ξ : Measure Gap) [IsFiniteMeasure ξ] {t : ℝ} (ht : 0 < t)
    (hs : ∀ᵐ d : Gap ∂ξ, t ≤ (d:ℝ)) :
    measureCostEntropy ξ ≤ ENNReal.ofReal ((K/t)*∫ d : Gap, (d:ℝ)⁻¹ ∂ξ) := by
  obtain ⟨N, hN, hbefore⟩ := exists_band_cutoff ht
  rw [measureCostEntropy_eq_prefix_of_support ξ hs hN]
  apply ENNReal.ofReal_le_ofReal
  have hw : ∑ j : Fin N, w j.rev.val ≤ 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i : Fin N => w i.val)).le.trans (hmass N)
  have hH := inverse_integrable_of_support ξ ht hs
  apply (costEntropy_le_reference (fun j : Fin N => bandCost_nonneg ξ j)
    (fun j => hpos j.rev.val) hw).trans
  have hband (j : Fin N) : bandCost ξ j * (1-log (w j.rev.val)) ≤
      (K/t) * ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂ξ := by
    rw [bandCost, ← integral_mul_const, ← integral_const_mul]
    apply integral_mono_ae ((band_inverseSquare_integrable ξ j).mul_const _)
      (hH.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem (measurableSet_band j), ae_restrict_of_ae hs] with d hd hd'
    calc
      _ ≤ (d:ℝ)⁻¹^2 * ((K/t) * (d:ℝ)) :=
        mul_le_mul_of_nonneg_left (hcoeff ht hbefore j d hd hd') (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j : Fin N, (K/t) * ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂ξ :=
      Finset.sum_le_sum (fun j _ => hband j)
    _ = (K/t) * ∑ j : Fin N, ∫ d : Gap in band j, (d:ℝ)⁻¹ ∂ξ := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← integral_iUnion_fintype (fun j : Fin N => measurableSet_band j)
        (fun i j hij => bands_disjoint (Fin.val_ne_iff.mpr hij))
        (fun _ => hH.integrableOn)]
      exact setIntegral_le_integral hH
        (Filter.Eventually.of_forall (fun d : Gap => inv_nonneg.mpr d.property.1.le))

/-- Lemma 2 of the certified-selection note. -/
theorem separated_cost : SeparatedCostStatement := by
  intro ξ _ t ht hs
  exact separated_cost_of_weights 2 (by norm_num) scaleWeight scaleWeight_pos scaleWeight_mass
    (@scaleWeight_band) ξ ht hs

end ThresholdHC.QuantileSelection
