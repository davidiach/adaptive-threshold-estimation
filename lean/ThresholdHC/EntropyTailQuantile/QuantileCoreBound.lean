import ThresholdHC.EntropyTail.CutDecomposition
import ThresholdHC.EntropyTail.EntropyMixture
import ThresholdHC.EntropyTail.ScaleSeparated

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

theorem quantileCore_entropy_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (σ : Measure Gap) (hσ : σ ≤ μ) :
    measureCostEntropy (quantileCore μ ρ) ≤ 2 * measureCostEntropy σ +
      ENNReal.ofReal ((8/quantileThreshold μ ρ) * ∫ d : Gap, (d:ℝ)⁻¹
        ∂upperCut (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ) (μ-σ)) := by
  let t := quantileThreshold μ ρ
  let r := quantileBoundaryFraction μ ρ
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  have ht := (quantileThreshold_properties μ hρ hρ1).1
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have : IsFiniteMeasure (upperCut t r σ) := isFiniteMeasure_of_le σ (upperCut_le t hr.1 hr.2.1 σ)
  have : IsFiniteMeasure (upperCut t r (μ-σ)) :=
    isFiniteMeasure_of_le (μ-σ) (upperCut_le t hr.1 hr.2.1 (μ-σ))
  have hd : quantileCore μ ρ = upperCut t r σ + upperCut t r (μ-σ) := by
    rw [← upperCut_add, add_comm σ, Measure.sub_add_cancel_of_le hσ]
    exact quantileCore_eq_upperCut μ hρ hρ1
  rw [hd]
  apply (measureCostEntropy_add_le_two _ _).trans
  apply add_le_add
  · exact mul_le_mul_right (measureCostEntropy_mono (upperCut_le t hr.1 hr.2.1 σ)) (2:ℝ≥0∞)
  · calc
      _ ≤ 2 * ENNReal.ofReal ((4/t) * ∫ d : Gap, (d:ℝ)⁻¹ ∂upperCut t r (μ-σ)) :=
        mul_le_mul_right (scaleSeparated_entropy _ ht (upperCut_support t r (μ-σ))) (2:ℝ≥0∞)
      _ = _ := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        dsimp [t, r]
        ring

theorem quantileTail_threshold_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ h : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h)
    (hht : h < quantileThreshold μ ρ) :
    h*ρ/quantileThreshold μ ρ ≤ tailModulus (quantileTail μ ρ) h := by
  have ht := (quantileThreshold_properties μ hρ hρ1).1
  have : IsFiniteMeasure (quantileTail μ ρ) := isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  calc
    h*ρ/quantileThreshold μ ρ = ∫ _ : Gap, h/quantileThreshold μ ρ ∂quantileTail μ ρ := by
      rw [integral_const, smul_eq_mul, measureReal_def, quantileTail_mass μ hρ hρ1,
        ENNReal.toReal_ofReal hρ.le]
      ring
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) (tailKernel_integrable _ hh)
      filter_upwards [quantileTail_support μ ρ] with d hd
      apply le_min
      · exact (div_le_one ht).2 hht.le
      · exact div_le_div_of_nonneg_left hh d.property.1 hd

theorem quantileCore_residual_work (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ h : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h)
    (hht : h < quantileThreshold μ ρ) (σ : Measure Gap) :
    h * (∫ d : Gap, (d:ℝ)⁻¹
      ∂upperCut (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ) (μ-σ)) ≤
        tailModulus (μ-σ) h := by
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  rw [← tailModulus_eq_inverseCost _ ((upperCut_support _ _ (μ-σ)).mono
    (fun _ hd => hht.le.trans hd))]
  exact tailModulus_mono (upperCut_le _ hr.1 hr.2.1 (μ-σ)) hh

end ThresholdHC.EntropyTail
