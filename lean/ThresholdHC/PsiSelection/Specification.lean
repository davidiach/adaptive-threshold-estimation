import ThresholdHC.EntropyTail.Specification
import ThresholdHC.Confidence.Model
import ThresholdHC.ConfidenceTransfer.CommonPairRate

/-! Target types for the arbitrary-law statistical `Ψ` lower bound (v6
Theorem A.5) in the unchanged observable rare-event experiment.

The variational modulus `Ψ` is compared with the entropy–tail selection
functional `K` for every probability law on `(0,1/2]`. The two statistical
targets then state the `Ψ` lower bound for the minimax RMS risk and for the
minimax confidence radius, with an explicit coefficient and every positive
budget. Budgets count actual flips, rarity is global and magnitudes and signs
stay hidden. No external statistical theorem is a premise. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiSelection
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail

/-- `Ψ_{μ,ρ}(B^{-1/2}) ≤ K_{μ,ρ}(B)` for every law, rarity and positive budget. -/
def PsiSelectionStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B →
    rarePsi μ ρ (1 / Real.sqrt B) ≤ selection μ ρ B

/-- The RMS half of Theorem A.5: `10^{-17} Ψ_{μ,ρ}(B^{-1/2}) ≤ R_{μ,ρ}(B)`. -/
def PsiRiskLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) * rarePsi μ ρ (1 / Real.sqrt B) ≤
        rareMinimaxRisk μ ρ B

/-- The confidence half of Theorem A.5 at the scale `√(log(1/δ)/B)`. -/
def PsiConfidenceLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
      ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) *
          rarePsi μ ρ (ThresholdHC.Confidence.confidenceScale B δ) ≤
        ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ

end ThresholdHC.PsiSelection
