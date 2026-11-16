import ThresholdHC.PsiClosedForm.Full
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open scoped ENNReal
example : EntropyFreeOrderStatement := entropy_free_order
example : PsiClosedFormStatement := psi_closed_form
example : PsiTrivialRegimeStatement := psi_trivial_regime
example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ≤
      ThresholdHC.EntropyTail.selection μ ρ B ∧
    min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) ≤
      ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧
    min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ≤
      min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) :=
  entropy_free_order μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt 2) * rarePsi μ ρ (1 / Real.sqrt B) ∧
    rarePsi μ ρ (1 / Real.sqrt B) ≤
      min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ∧
    min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ≤
      min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) :=
  psi_closed_form μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (ht : ThresholdHC.EntropyTailQuantile.quantileThreshold μ ρ ≤ 1 / Real.sqrt B) :
    rarePsi μ ρ (1 / Real.sqrt B) = ENNReal.ofReal ρ ∧
    min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) =
      ENNReal.ofReal ρ :=
  psi_trivial_regime μ ρ B hρ hρ4 hB ht
#print axioms ThresholdHC.PsiClosedForm.EntropyFreeOrderStatement
#print axioms ThresholdHC.PsiClosedForm.PsiClosedFormStatement
#print axioms ThresholdHC.PsiClosedForm.PsiTrivialRegimeStatement
#print axioms ThresholdHC.PsiClosedForm.above_cutoff
#print axioms ThresholdHC.PsiClosedForm.allocation_le_rarePsi
#print axioms ThresholdHC.PsiClosedForm.closed_form_real
#print axioms ThresholdHC.PsiClosedForm.cutoff_lt_threshold
#print axioms ThresholdHC.PsiClosedForm.entropy_free_order
#print axioms ThresholdHC.PsiClosedForm.integrable_unit
#print axioms ThresholdHC.PsiClosedForm.inverseSquareCost
#print axioms ThresholdHC.PsiClosedForm.inverseSquareCost_le_gamma
#print axioms ThresholdHC.PsiClosedForm.kernel_pointwise
#print axioms ThresholdHC.PsiClosedForm.measurable_gapAllocation
#print axioms ThresholdHC.PsiClosedForm.measurable_rootAllocation
#print axioms ThresholdHC.PsiClosedForm.measurable_tailKernel
#print axioms ThresholdHC.PsiClosedForm.payoff_eq
#print axioms ThresholdHC.PsiClosedForm.psi_closed_form
#print axioms ThresholdHC.PsiClosedForm.psi_trivial_regime
#print axioms ThresholdHC.PsiClosedForm.quantileCore_le
#print axioms ThresholdHC.PsiClosedForm.quantileZero
#print axioms ThresholdHC.PsiClosedForm.quantileZero_le_closedQuantile
#print axioms ThresholdHC.PsiClosedForm.quantile_form_le
#print axioms ThresholdHC.PsiClosedForm.rareObjective_le_zero
#print axioms ThresholdHC.PsiClosedForm.rarePsi_le_selectionZero
#print axioms ThresholdHC.PsiClosedForm.rootAllocation
#print axioms ThresholdHC.PsiClosedForm.rootAllocation_le_one
#print axioms ThresholdHC.PsiClosedForm.rootAllocation_pos
#print axioms ThresholdHC.PsiClosedForm.rootAllocation_sq
#print axioms ThresholdHC.PsiClosedForm.root_sum_le
#print axioms ThresholdHC.PsiClosedForm.selectionZero
#print axioms ThresholdHC.PsiClosedForm.selectionZero_le_quantileZero
#print axioms ThresholdHC.PsiClosedForm.selectionZero_le_selection
#print axioms ThresholdHC.PsiClosedForm.sub_quantileCore
#print axioms ThresholdHC.PsiClosedForm.tailKernel
#print axioms ThresholdHC.PsiClosedForm.tailKernel_le_one
#print axioms ThresholdHC.PsiClosedForm.tailKernel_nonneg
