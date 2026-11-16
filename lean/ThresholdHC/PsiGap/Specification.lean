import ThresholdHC.PsiClosedForm.Specification

/-! Target types for the distance of the variational modulus `Ψ` from the rate
(v6 Theorem 14.11), for every probability law on `(0,1/2]`.

The quantile core `κ` has inverse-square cost `A_κ` and cost entropy
`Γ_κ = A_κ (1 + E_κ)`, where `E_κ` is the Shannon entropy of its normalized
band costs. The closed quantile functional `Q` is then at most
`√(1 + E_κ) Q⁰`, hence at most `√(2 (1 + E_κ)) Ψ`, and under two conditions
the factor `√(1 + E_κ)` is attained within a factor two. The statistical
statements use the checked coefficients `10^{-17}` and `30001` for `Q` in the
unchanged observable rare-event experiment; the paper's display uses its own
upper constant. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiGap
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile (quantileTail quantileCore quantileThreshold
  closedQuantileValue measureCostEntropy)

/-- The inverse-square cost `A_κ` of the quantile core, as a real number. -/
def coreCost (μ : Measure Gap) (ρ : ℝ) : ℝ :=
  (inverseSquareCost (quantileCore μ ρ)).toReal

/-- The entropy `E_κ` of the normalized band costs of the quantile core. -/
def coreEntropy (μ : Measure Gap) (ρ : ℝ) : ℝ :=
  ∑' j : ℕ, Real.negMulLog
    (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / coreCost μ ρ)

/-- `0 < A_κ < ∞`, `E_κ ≥ 0`, `Γ_κ = A_κ (1 + E_κ)` and
`E_κ ≤ log log₂(1/t)` for the quantile threshold `t`. -/
def CoreEntropyStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ → ρ ≤ 1/4 →
    0 < coreCost μ ρ ∧
    inverseSquareCost (quantileCore μ ρ) = ENNReal.ofReal (coreCost μ ρ) ∧
    0 ≤ coreEntropy μ ρ ∧
    measureCostEntropy (quantileCore μ ρ) =
      ENNReal.ofReal (coreCost μ ρ * (1 + coreEntropy μ ρ)) ∧
    coreEntropy μ ρ ≤ Real.log (Real.logb 2 (1 / quantileThreshold μ ρ))

/-- The chain (W4): `Ψ ≤ K ≤ Q ≤ √(1+E_κ) Q⁰` and `Q ≤ √(2(1+E_κ)) Ψ`. -/
def PsiGapStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      rarePsi μ ρ (1 / Real.sqrt B) ≤ ThresholdHC.EntropyTail.selection μ ρ B ∧
      ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
      closedQuantileValue μ ρ B ≤
        ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ)) * quantileZero μ ρ B ∧
      closedQuantileValue μ ρ B ≤
        ENNReal.ofReal (Real.sqrt (2 * (1 + coreEntropy μ ρ))) *
          rarePsi μ ρ (1 / Real.sqrt B)

/-- The minimax RMS risk lies between `10^{-17} Ψ` and `30001 √(2(1+E_κ)) Ψ`. -/
def PsiGapRiskStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) * rarePsi μ ρ (1 / Real.sqrt B) ≤
        rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤
        ENNReal.ofReal (30001 * Real.sqrt (2 * (1 + coreEntropy μ ρ))) *
          rarePsi μ ρ (1 / Real.sqrt B)

/-- When the core term dominates the tail term and the cap `ρ` is inactive,
`Q ≥ ½ √(1+E_κ) Q⁰`, and the minimax RMS risk is at least
`(10^{-17}/2) √(1+E_κ) Ψ`. -/
def PsiGapReverseStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) ≤
      ENNReal.ofReal (1 / Real.sqrt B) *
        (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ) →
    ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
      ENNReal.ofReal (1 / Real.sqrt B) *
        (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ) ≤
      ENNReal.ofReal ρ →
      ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ) / 2) * quantileZero μ ρ B ≤
        closedQuantileValue μ ρ B ∧
      ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17 * (Real.sqrt (1 + coreEntropy μ ρ) / 2)) *
          rarePsi μ ρ (1 / Real.sqrt B) ≤
        rareMinimaxRisk μ ρ B

end ThresholdHC.PsiGap
