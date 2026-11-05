import ThresholdHC.QuantileSharpLaw.OutwardGeometry
import ThresholdHC.EntropyTailQuantile.ScaleSeparated

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

theorem outward_core_work (Z : Measure Gap) [IsFiniteMeasure Z] {t : ℝ} (ht : 0 < t)
    (n : ℕ) (hthigh : t ≤ bandEdge n) (hZ : ∀ᵐ d : Gap ∂Z, t ≤ (d : ℝ)) :
    t*fullCoreCost n (outwardCosts n (bandCost Z)) ≤ ∫ d : Gap, (d : ℝ)⁻¹ ∂Z := by
  have hH := inverse_integrable_of_support Z ht hZ
  let H := fun j : ℕ => ∫ d : Gap in band j, (d : ℝ)⁻¹ ∂Z
  have hpiece (j : ℕ) (c : ℝ) (hcoeff : ∀ᵐ d : Gap ∂Z.restrict (band j), c ≤ (d : ℝ)) :
      c*bandCost Z j ≤ H j := by
    unfold H bandCost
    rw [← integral_const_mul]
    apply integral_mono_ae ((band_inverseSquare_integrable Z j).const_mul c) hH.integrableOn
    filter_upwards [hcoeff] with d hd
    calc
      c*(d : ℝ)⁻¹^2 ≤ (d : ℝ)*(d : ℝ)⁻¹^2 :=
        mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      _ = (d : ℝ)⁻¹ := by
        rw [pow_two,← mul_assoc,mul_inv_cancel₀ d.property.1.ne',one_mul]
  have hband (i : Option (Fin n)) :
      t*(coreWeight i*outwardCosts n (bandCost Z) i) ≤ outwardCosts n H i := by
    cases i with
    | none =>
      change t*(1*bandCost Z n) ≤ H n
      rw [one_mul]
      exact hpiece n t (ae_restrict_of_ae hZ)
    | some i =>
      change t*((2 : ℝ)^i.val*bandCost Z i.rev.val) ≤ H i.rev.val
      rw [← mul_assoc]
      apply hpiece
      filter_upwards [ae_restrict_mem (measurableSet_band i.rev.val)] with d hd
      exact outward_band_lower hthigh i d hd
  calc
    _ = ∑ i, t*(coreWeight i*outwardCosts n (bandCost Z) i) := by
      rw [fullCoreCost_eq_sum,Finset.mul_sum]
    _ ≤ ∑ i, outwardCosts n H i := Finset.sum_le_sum (fun i _ => hband i)
    _ = ∑ j : Fin (n+1), H j.val := outwardCosts_sum n H id
    _ ≤ _ := by
      unfold H
      rw [← integral_iUnion_fintype (fun j : Fin (n+1) => measurableSet_band j.val)
        (fun i j hij => bands_disjoint (Fin.val_ne_iff.mpr hij)) (fun _ => hH.integrableOn)]
      exact setIntegral_le_integral hH
        (Filter.Eventually.of_forall (fun d : Gap => inv_nonneg.mpr d.property.1.le))

end ThresholdHC.QuantileSharpLaw
