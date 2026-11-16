import ThresholdHC.PsiGap.Full
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiGap
open ThresholdHC.EntropyTailQuantile (quantileTail quantileCore quantileThreshold
  closedQuantileValue measureCostEntropy)
open scoped ENNReal
example : CoreEntropyStatement := core_entropy
example : PsiGapStatement := psi_gap
example : PsiGapReverseStatement := psi_gap_reverse
example : PsiGapRiskStatement := psi_gap_risk
example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    0 < (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal ∧
    (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ) = ENNReal.ofReal (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal ∧
    0 ≤ (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal)) ∧
    measureCostEntropy (quantileCore μ ρ) = ENNReal.ofReal ((∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal * (1 + (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal)))) ∧
    (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal)) ≤ Real.log (Real.logb 2 (1 / quantileThreshold μ ρ)) :=
  core_entropy μ ρ hρ hρ4

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    rarePsi μ ρ (1 / Real.sqrt B) ≤ ThresholdHC.EntropyTail.selection μ ρ B ∧
    ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (Real.sqrt (1 + (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal)))) * (min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂quantileCore μ ρ) ^ (1/2 : ℝ))) ∧
    closedQuantileValue μ ρ B ≤
      ENNReal.ofReal (Real.sqrt (2 * (1 + (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal))))) * rarePsi μ ρ (1 / Real.sqrt B) :=
  psi_gap μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) * rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤
      ENNReal.ofReal (30001 * Real.sqrt (2 * (1 + (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal))))) * rarePsi μ ρ (1 / Real.sqrt B) :=
  psi_gap_risk μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (htail : ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) ≤
      ENNReal.ofReal (1 / Real.sqrt B) *
        (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ) ^ (1/2 : ℝ))
    (hcap : ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
      ENNReal.ofReal (1 / Real.sqrt B) *
        (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ) ≤
      ENNReal.ofReal ρ) :
    ENNReal.ofReal (Real.sqrt (1 + (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal))) / 2) * (min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂quantileCore μ ρ) ^ (1/2 : ℝ))) ≤ closedQuantileValue μ ρ B ∧
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17 * (Real.sqrt (1 + (∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal))) / 2)) *
        rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B :=
  psi_gap_reverse μ ρ B hρ hρ4 hB htail hcap
#print axioms ThresholdHC.PsiGap.CoreEntropyStatement
#print axioms ThresholdHC.PsiGap.PsiGapReverseStatement
#print axioms ThresholdHC.PsiGap.PsiGapRiskStatement
#print axioms ThresholdHC.PsiGap.PsiGapStatement
#print axioms ThresholdHC.PsiGap.closedQuantile_eq
#print axioms ThresholdHC.PsiGap.closedQuantile_le_root_psi
#print axioms ThresholdHC.PsiGap.closedQuantile_le_root_quantileZero
#print axioms ThresholdHC.PsiGap.coreCost
#print axioms ThresholdHC.PsiGap.coreEntropy
#print axioms ThresholdHC.PsiGap.core_bands
#print axioms ThresholdHC.PsiGap.core_entropy
#print axioms ThresholdHC.PsiGap.core_entropy_real
#print axioms ThresholdHC.PsiGap.core_root
#print axioms ThresholdHC.PsiGap.one_le_root
#print axioms ThresholdHC.PsiGap.psi_gap
#print axioms ThresholdHC.PsiGap.psi_gap_reverse
#print axioms ThresholdHC.PsiGap.psi_gap_risk
#print axioms ThresholdHC.PsiGap.sqrt_two_mul
