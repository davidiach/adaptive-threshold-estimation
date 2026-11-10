import ThresholdHC.PsiSelection.Comparison
import ThresholdHC.EntropyTailSharp.Full
import ThresholdHC.ConfidenceEntropy.Full

/-! The arbitrary-law statistical `Ψ` lower bound as a corollary of the checked
entropy–tail law. The deterministic comparison `Ψ ≤ K` is composed with the
explicit entropy–tail lower bound for the minimax RMS risk and with the explicit
entropy–tail lower bound for the minimax confidence radius. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiSelection
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail

theorem psi_le_selection : PsiSelectionStatement := by
  intro μ _ ρ B hB
  exact rarePsi_le_selection_scale μ ρ hB

theorem psi_risk_lower : PsiRiskLowerStatement := by
  intro μ _ ρ B hρ hρ4 hB
  exact (mul_le_mul_right (rarePsi_le_selection_scale μ ρ hB) _).trans
    (EntropyTailSharp.entropy_tail_explicit_law μ ρ B hρ hρ4 hB).1

/-- The confidence scale is the resolution of the effective budget `B/log(1/δ)`. -/
theorem confidenceScale_eq {B δ : ℝ} :
    ThresholdHC.Confidence.confidenceScale B δ = 1 / Real.sqrt (B / Real.log (1/δ)) := by
  unfold ThresholdHC.Confidence.confidenceScale
  rw [one_div (Real.sqrt (B / Real.log (1/δ))), ← Real.sqrt_inv, inv_div]

theorem psi_confidence_lower : PsiConfidenceLowerStatement := by
  intro μ _ ρ B δ hρ hρ4 hB hδ hδ4
  rw [confidenceScale_eq]
  exact (mul_le_mul_right (rarePsi_le_selection_scale μ ρ
      (div_pos hB (ThresholdHC.Confidence.confidence_log_pos hδ hδ4))) _).trans
    (ConfidenceEntropy.entropy_tail_confidence_lower_explicit μ hρ hρ4 hB hδ hδ4)

end ThresholdHC.PsiSelection
