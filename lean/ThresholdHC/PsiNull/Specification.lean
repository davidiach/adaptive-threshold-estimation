import ThresholdHC.ConfidenceLocalization.Obstruction
import ThresholdHC.ObservableSimulation.OriginalExperiment
import ThresholdHC.RareAboveTwo.Model

/-! Target statements for Proposition prop:psi-null (v6, appendix on transfer
foundations, eq:psi-null-product) and its corollary eq:psi-budget-lower (v6,
appendix on the entropy-tail lower bound).

Proposition prop:psi-null bounds the null-work obstruction
`J₀(b) ≥ sup_{h>0} (Ψ_{μ,ρ}(h) - 4b)_+² / (192h²)` for every probability law `μ`
of gaps on `(0,1/2]` and every `0 ≤ b ≤ ρ/64`. Here `J₀(b) ≥ J` is
`NullVarianceObstruction μ p₀ p₁ ρ b J` with the original coin parameters
`p₀ d = 1/2 - d` and `p₁ d = 1/2 + d`, and `Ψ_{μ,ρ}(h)` is `rarePsi μ ρ h`. The
supremum over `h` is expressed pointwise in `h`: the statement asserts the
obstruction with `J = (Ψ(h) - 4b)_+²/(192h²)` for every `h > 0`. This is
equivalent to the supremum form, since `J₀(b)` bounds a supremum exactly when it
bounds every term, and it also covers an infinite supremum. The rarity range
`0 < ρ ≤ 1/4` is the paper's standing assumption on the prior class `X_ρ` and is
an explicit hypothesis.

The corollary eq:psi-budget-lower reads `R_{μ,ρ}(B) ≥ Ψ_{μ,ρ}(B^{-1/2})/8192` for
every budget `B > 0`, with `B^{-1/2}` written `1 / Real.sqrt B`. The proofs are in
`Full.lean`. -/
noncomputable section
namespace ThresholdHC.PsiNull
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.ConfidenceLocalization ThresholdHC.ObservableSimulation
  ThresholdHC.RareAboveTwo

/-- Proposition prop:psi-null (eq:psi-null-product), pointwise in the resolution
`h > 0`: for `0 < ρ ≤ 1/4` and `0 ≤ b ≤ ρ/64`, the null-work obstruction holds
with `J = (Ψ_{μ,ρ}(h) - 4b)_+² / (192h²)`. -/
def PsiNullStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ b h : ℝ), 0 < ρ → ρ ≤ 1/4 →
    0 ≤ b → b ≤ ρ/64 → 0 < h →
    NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b
      ((max ((rarePsi μ ρ h).toReal - 4*b) 0)^2 / (192*h^2))

/-- eq:psi-budget-lower: `R_{μ,ρ}(B) ≥ Ψ_{μ,ρ}(B^{-1/2})/8192` for `0 < ρ ≤ 1/4`
and every budget `B > 0`. -/
def PsiBudgetLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal (1/8192) * rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B

end ThresholdHC.PsiNull
