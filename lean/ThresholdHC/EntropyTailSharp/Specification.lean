import ThresholdHC.EntropyTail.Specification

/-! Explicit comparison for the original observable minimax experiment. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.EntropyTailSharp
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail

def ExplicitLawStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) * selection μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
        rareMinimaxRisk μ ρ B ≤ 28000 * selection μ ρ B

end ThresholdHC.EntropyTailSharp
