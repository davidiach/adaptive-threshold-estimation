import ThresholdHC.RareAboveTwo.Model
import ThresholdHC.EntropyTailQuantile.Model

/-! Target statements for the two corollaries of the finite-gap manuscript
(`paper/finite-gap-rare-events`, Section `sec:consequences`; revision 2 and
the v6 copy have the same text).

* Corollary `cor:one-gap`: at a point mass the rare-event minimax risk is of
  order `min{ρ, √ρ/(d√B)}`. The constants `10^{-17}` and `28000` are those of
  the explicit entropy–tail law; the manuscript's own proof through its
  Theorem 1.1 gives weaker constants.
* Corollary `cor:mse`, both displays: for every finitely supported law the
  squared minimax risk lies between `c_0^2` and `2 C_0^2` times
  `min{ρ^2, T_h^2 + ρ Γ_κ/B}`, with `c_0 = 10^{-20}` and `C_0 = 30001`; when
  `B ≥ d^{-2}` at every atom, `T_h = h J_ν` and the bracket becomes
  `min{ρ^2, (J_ν^2 + ρ Γ_κ)/B}`.

The proofs are in `Corollaries.lean`. -/
noncomputable section
namespace ThresholdHC.FiniteGapCorollaries
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open scoped ENNReal

/-- Corollary `cor:one-gap` with the entropy–tail constants. -/
def OneGapStatement : Prop :=
  ∀ (d : Gap) (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17 * aboveTwoRate (d : ℝ) ρ B) ≤
        rareMinimaxRisk (Measure.dirac d) ρ B ∧
      rareMinimaxRisk (Measure.dirac d) ρ B ≤ ENNReal.ofReal (28000 * aboveTwoRate (d : ℝ) ρ B)

/-- The first display of Corollary `cor:mse`: with `T_h` the tail modulus of
the quantile tail at `h = B^{-1/2}` and `Γ_κ` the cost entropy of the quantile
core. -/
def MeanSquareStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    let M := min (ENNReal.ofReal ρ ^ 2)
      (ENNReal.ofReal (tailModulus (quantileTail μ ρ) (EntropyTailQuantile.budgetScale B)) ^ 2 +
        ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ) / ENNReal.ofReal B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M ≤ (rareMinimaxRisk μ ρ B) ^ 2 ∧
      (rareMinimaxRisk μ ρ B) ^ 2 ≤ 2 * 30001 ^ 2 * M

/-- The second display of Corollary `cor:mse`: if `B ≥ d^{-2}` at every
support point `d` (the support of a finitely supported law is its set of
atoms, so this is the manuscript's `B ≥ d_1^{-2}`), the bounds of the first
display hold with the bracket `min{ρ^2, (J_ν^2 + ρ Γ_κ)/B}`, where
`J_ν = ∫ d^{-1} ν(dd)`, because then `T_h = h J_ν`. -/
def LargeBudgetMeanSquareStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → (∀ d ∈ μ.support, ((d : ℝ) ^ 2)⁻¹ ≤ B) →
    let J := ∫ d : Gap, (d : ℝ)⁻¹ ∂(quantileTail μ ρ)
    let M := min (ENNReal.ofReal ρ ^ 2)
      ((ENNReal.ofReal J ^ 2 + ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) /
        ENNReal.ofReal B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M ≤ (rareMinimaxRisk μ ρ B) ^ 2 ∧
      (rareMinimaxRisk μ ρ B) ^ 2 ≤ 2 * 30001 ^ 2 * M

end ThresholdHC.FiniteGapCorollaries
