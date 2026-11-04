import ThresholdHC.ShiftedPower.Lower
import ThresholdHC.ShiftedPower.Confidence

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.Confidence
open ThresholdHC.ConfidenceTransfer ThresholdHC.ConfidenceProgram

/-- The logarithmic row holds at all positive budgets. Its confidence
upper construction also obeys a deterministic cap on purchased flips. -/
theorem linear_rates (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ B δ : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hm : ExactPowerLaw μ 1 a) (hr : 0 < ρ) (hu : ρ ≤ 1/4)
    (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let z := linearRate ρ ((sqrt B)⁻¹/a)
    let w := linearRate ρ (confidenceScale B δ/a)
    (ENNReal.ofReal (z/32) ≤ rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (linearConstant*z)) ∧
    (ENNReal.ofReal (w/960) ≤ rareConfidenceRadius μ ρ B δ ∧
      rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (27*linearConstant*w)) := by
  have hlow := linear_lower μ hm ha hr hu hB hd hd'
  have hp := exactPower_margin μ 1 a hm
  refine ⟨⟨hlow.1,?_⟩,⟨hlow.2,expected_confidence_le_hard μ hB.le,?_⟩⟩
  · obtain ⟨R,mR,A,hA⟩ := linear_rms_family ha ha' hr (by linarith) hB
    obtain ⟨hw,hR⟩ := hA μ hp
    exact le_trans (sInf_le (show rareRisk μ A ρ ∈ _ from ⟨R,mR,A,hw,rfl⟩)) hR
  · obtain ⟨R,mR,A,hcap,hA⟩ := linear_confidence_family ha ha' hr (by linarith) hB hd hd'
    obtain ⟨_,hf⟩ := hA μ hp
    have hw : 0 ≤ linearRate ρ (confidenceScale B δ/a) :=
      linearRate_nonneg hr.le (div_nonneg (sqrt_nonneg _) ha.le)
    exact sInf_le ⟨R,mR,A,_,mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans linearConstant_ge_one)) hw,hcap,hf,rfl⟩

/-- All constants are independent of the actual law, rarity, scale and
budget. Their dependence on α is displayed by intermediateConstant. -/
theorem intermediate_rates (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B δ : ℝ}
    (hα : 1 < α) (hu : α < 2) (ha : 0 < a) (ha' : a ≤ 1) (hm : ExactPowerLaw μ α a)
    (hr : 0 < ρ) (hr' : ρ ≤ 1/4) (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let z := intermediateRate α ρ ((sqrt B)⁻¹/a)
    let w := intermediateRate α ρ (confidenceScale B δ/a)
    (ENNReal.ofReal (z/32) ≤ rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (intermediateConstant α*z)) ∧
    (ENNReal.ofReal (w/960) ≤ rareConfidenceRadius μ ρ B δ ∧
      rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (27*intermediateConstant α*w)) := by
  have hlow := intermediate_lower μ hm (by linarith) ha hr hr' hB hd hd'
  have hp := exactPower_margin μ α a hm
  refine ⟨⟨hlow.1,?_⟩,⟨hlow.2,expected_confidence_le_hard μ hB.le,?_⟩⟩
  · obtain ⟨R,mR,A,hA⟩ := intermediate_rms_family hα hu ha ha' hr (by linarith) hB
    obtain ⟨hw,hR⟩ := hA μ hp
    exact le_trans (sInf_le (show rareRisk μ A ρ ∈ _ from ⟨R,mR,A,hw,rfl⟩)) hR
  · obtain ⟨R,mR,A,hcap,hA⟩ := intermediate_confidence_family hα hu ha ha' hr (by linarith) hB hd hd'
    obtain ⟨_,hf⟩ := hA μ hp
    have hw : 0 ≤ intermediateRate α ρ (confidenceScale B δ/a) :=
      intermediateRate_nonneg hr.le (div_nonneg (sqrt_nonneg _) ha.le)
    exact sInf_le ⟨R,mR,A,_,mul_nonneg (mul_nonneg (by norm_num)
      (zero_le_one.trans (intermediateConstant_ge_one hα))) hw,hcap,hf,rfl⟩

end ThresholdHC.ShiftedPower
