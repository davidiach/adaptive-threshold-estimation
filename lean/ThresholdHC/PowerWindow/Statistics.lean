import ThresholdHC.PowerWindow.CoreCost
import ThresholdHC.PsiGap.Full

/-! The statistical composition is conditional on the uniform deterministic
quantile comparison. It does not supply that still-unproved comparison. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

theorem power_risk_of_quantile (hQ : PowerQuantileStatement) : PowerRiskStatement := by
  intro μ _ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm
  obtain ⟨hlo, hhi⟩ := hQ μ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm
  constructor
  · have h := (mul_le_mul_right hlo (ENNReal.ofReal ((10 : ℝ)⁻¹^17))).trans
      (ThresholdHC.EntropyTailSharp.closed_quantile_lower_explicit μ hρ hρ4 hB)
    rw [← ENNReal.ofReal_mul (by positivity)] at h
    convert h using 1
    congr 1
    ring
  · have h := (ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001 μ hρ hρ4 hB).trans
      (mul_le_mul_right hhi (ENNReal.ofReal 30001))
    rw [← ENNReal.ofReal_mul (by norm_num)] at h
    convert h using 1
    congr 1
    ring

theorem power_confidence_of_quantile (hQ : PowerQuantileStatement) : PowerConfidenceStatement := by
  intro μ _ α a ρ B δ hα hα4 ha ha2 hρ hρ4 hB hδ hδ4 hm
  have hlog := ThresholdHC.Confidence.confidence_log_pos hδ hδ4
  have hβ := div_pos hB hlog
  have hx : 1 / (a * Real.sqrt (B / Real.log (1/δ))) =
      Real.sqrt (Real.log (1/δ) / B) / a := by
    rw [one_div, mul_inv, ← Real.sqrt_inv, inv_div]
    ring
  obtain ⟨hlo, hhi⟩ := hQ μ α a ρ (B / Real.log (1/δ))
    hα hα4 ha ha2 hρ hρ4 hβ hm
  rw [hx] at hlo hhi
  refine ⟨?_, ThresholdHC.ConfidenceProgram.expected_confidence_le_hard μ hB.le, ?_⟩
  · have h := (mul_le_mul_right hlo (ENNReal.ofReal ((10 : ℝ)⁻¹^17))).trans
      (ThresholdHC.ConfidenceEntropy.closed_quantile_confidence_lower μ hρ hρ4 hB hδ hδ4)
    rw [← ENNReal.ofReal_mul (by positivity)] at h
    convert h using 1
    congr 1
    ring
  · have hK := (ThresholdHC.EntropyTail.selection_quantile_comparison μ hρ hρ4 hβ).1
    have hupper : ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤
        ENNReal.ofReal 750000 * ThresholdHC.EntropyTail.selection μ ρ (B / Real.log (1/δ)) := by
      simpa only [ENNReal.ofReal_ofNat] using
        ThresholdHC.ConfidenceProgram.general_hard_confidence_upper μ hρ hρ4 hB hδ hδ4
    have h := hupper.trans
      (mul_le_mul_right (hK.trans hhi) (ENNReal.ofReal 750000))
    rw [← ENNReal.ofReal_mul (by norm_num)] at h
    convert h using 1
    congr 1
    ring

end ThresholdHC.PowerWindow
