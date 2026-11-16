import ThresholdHC.PsiSelection.Specification
import ThresholdHC.EntropyTailQuantile.Model

/-! Target types for the closed form of the variational modulus `Ψ` (v6
Proposition 14.9), for every probability law on `(0,1/2]`.

The entropy-free functionals of display (W1) are the selection functional `K`
and the closed quantile functional `Q` with the cost entropy `Γ_σ` replaced by
the inverse-square cost `A_σ = ∫ d^{-2} dσ`. The quantile split, with its
fractional boundary atom, is the one already defined for `Q`. The scale is
`h = B^{-1/2}`, which ranges over every positive resolution. All values are
extended nonnegative reals. The statements are deterministic: no experiment
and no estimator occurs in them. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiClosedForm
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- The inverse-square cost `A_σ = ∫ d^{-2} dσ`. -/
def inverseSquareCost (σ : Measure Gap) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ

/-- `K⁰_{μ,ρ}(B)`: the selection functional with `A_σ` in place of `Γ_σ`. -/
def selectionZero (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
    ENNReal.ofReal (1 / Real.sqrt B) * (ENNReal.ofReal ρ * inverseSquareCost σ) ^ (1/2 : ℝ)
      + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B))

/-- `Q⁰_{μ,ρ}(B) = min{ρ, T_h + h√(ρ A_κ)}` on the quantile split `μ = ν + κ`. -/
def quantileZero (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal ρ)
    (ThresholdHC.EntropyTail.tailCost
        (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
      ENNReal.ofReal (1 / Real.sqrt B) *
        (ENNReal.ofReal ρ *
          inverseSquareCost (ThresholdHC.EntropyTailQuantile.quantileCore μ ρ)) ^ (1/2 : ℝ))

/-- The comparisons stated after (W1): `K⁰ ≤ K`, `Q⁰ ≤ Q` and `K⁰ ≤ Q⁰`. -/
def EntropyFreeOrderStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      selectionZero μ ρ B ≤ ThresholdHC.EntropyTail.selection μ ρ B ∧
      quantileZero μ ρ B ≤ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧
      selectionZero μ ρ B ≤ quantileZero μ ρ B

/-- The chain (W2): `Q⁰/√2 ≤ Ψ ≤ K⁰ ≤ Q⁰`, with the first inequality written
as `Q⁰ ≤ √2 Ψ`. -/
def PsiClosedFormStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      quantileZero μ ρ B ≤ ENNReal.ofReal (Real.sqrt 2) * rarePsi μ ρ (1 / Real.sqrt B) ∧
      rarePsi μ ρ (1 / Real.sqrt B) ≤ selectionZero μ ρ B ∧
      selectionZero μ ρ B ≤ quantileZero μ ρ B

/-- The first sharpness statement of Proposition 14.9: when the resolution is
at least the quantile threshold, `Ψ = Q⁰ = ρ`. -/
def PsiTrivialRegimeStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
      ThresholdHC.EntropyTailQuantile.quantileThreshold μ ρ ≤ 1 / Real.sqrt B →
        rarePsi μ ρ (1 / Real.sqrt B) = ENNReal.ofReal ρ ∧
        quantileZero μ ρ B = ENNReal.ofReal ρ

end ThresholdHC.PsiClosedForm
