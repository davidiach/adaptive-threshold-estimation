import ThresholdHC.PsiSelection.Full
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiSelection
open scoped ENNReal
example : PsiConfidenceLowerStatement := psi_confidence_lower
example : PsiSelectionStatement := psi_le_selection
example : PsiRiskLowerStatement := psi_risk_lower
example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) :
    rarePsi μ ρ (1 / Real.sqrt B) ≤ ThresholdHC.EntropyTail.selection μ ρ B :=
  psi_le_selection μ ρ B hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) * rarePsi μ ρ (1 / Real.sqrt B) ≤
      rareMinimaxRisk μ ρ B :=
  psi_risk_lower μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B δ : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) *
        rarePsi μ ρ (Real.sqrt (Real.log (1/δ) / B)) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ :=
  psi_confidence_lower μ ρ B δ hρ hρ4 hB hδ hδ4
#print axioms ThresholdHC.PsiSelection.PsiConfidenceLowerStatement
#print axioms ThresholdHC.PsiSelection.PsiRiskLowerStatement
#print axioms ThresholdHC.PsiSelection.PsiSelectionStatement
#print axioms ThresholdHC.PsiSelection.confidenceScale_eq
#print axioms ThresholdHC.PsiSelection.ofReal_sqrt_sq
#print axioms ThresholdHC.PsiSelection.psi_confidence_lower
#print axioms ThresholdHC.PsiSelection.psi_le_selection
#print axioms ThresholdHC.PsiSelection.psi_risk_lower
#print axioms ThresholdHC.PsiSelection.rareObjective_le
#print axioms ThresholdHC.PsiSelection.rarePsi_le_selection_scale
