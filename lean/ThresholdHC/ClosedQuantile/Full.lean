import ThresholdHC.ClosedQuantile.Specification
import ThresholdHC.EntropyTail.Law

/-! Universal closed-quantile minimax corollary of the completed entropy-tail
law and the deterministic quantile comparison, in the original experiment. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ClosedQuantile
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile

theorem closed_quantile_law : ClosedQuantileLawStatement := by
  obtain ⟨c,hc,hl⟩ := ThresholdHC.EntropyTail.entropy_tail_lower
  let D : ℝ := 1+2*Real.sqrt 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨c/D,30001,div_pos hc hD,by norm_num,?_⟩
  intro ρ B hρ hρ4 hB μ _
  constructor
  · have hQ := (ThresholdHC.EntropyTail.selection_quantile_comparison μ hρ hρ4 hB).2
    calc
      ENNReal.ofReal (c/D)*closedQuantileValue μ ρ B ≤
          ENNReal.ofReal (c/D)*(ENNReal.ofReal D*ThresholdHC.EntropyTail.selection μ ρ B) :=
        mul_le_mul' le_rfl hQ
      _ = ENNReal.ofReal c*ThresholdHC.EntropyTail.selection μ ρ B := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (div_nonneg hc.le hD.le),
          div_mul_cancel₀ c hD.ne']
      _ ≤ rareMinimaxRisk μ ρ B := hl ρ B hρ hρ4 hB μ
  · exact ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001 μ hρ hρ4 hB

end ThresholdHC.ClosedQuantile
