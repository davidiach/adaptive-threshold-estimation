import ThresholdHC.EntropyTailBridge.Compatibility
import ThresholdHC.EntropyTailExecution.UpperTheorem

/-! Transfer the upper theorem and deterministic quantile comparison to the
separately frozen interface on main. No statistical lower bound is assumed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTailBridge
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

theorem canonical_entropy_tail_upper : EntropyTail.EntropyTailUpperStatement := by
  refine ⟨28000, by norm_num, ?_⟩
  intro ρ B hρ hρ1 hB μ _
  rw [canonical_selection_eq]
  exact EntropyTailExecution.entropy_tail_upper_28000 μ hρ hρ1 hB

theorem canonical_quantile_comparison (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (1+2*Real.sqrt 2) *
      EntropyTail.selection μ ρ B := by
  rw [canonical_selection_eq]
  exact quantile_comparison μ ρ B hρ hρ1 hB

end ThresholdHC.EntropyTailBridge
