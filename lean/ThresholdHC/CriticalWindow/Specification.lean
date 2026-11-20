import ThresholdHC.PowerWindow.Specification
import ThresholdHC.CriticalEntropy.CriticalModel

/-! Target statements for Corollary 14.14 (the critical window) and Remark 14.15
(reading the uniform rate) of v6 §14.8. They use only the uniform power-law
definitions of `PowerWindow`, the rare-event minimax risk, the variational
modulus `Ψ` and the critical log factor. The proofs are in the other modules of
this directory. -/
noncomputable section
namespace ThresholdHC.CriticalWindow
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow
open scoped ENNReal

/-- Corollary 14.14, deterministic part: on the window `3/2 ≤ α ≤ 3` the uniform
rate (W7) is `min{ρ, Y}` within the factor `5.13`. -/
def WindowRateStatement : Prop :=
  ∀ (α ρ x : ℝ), 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 → 0 < x →
    let Y := x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ)))
    min ρ Y ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ 513/100 * min ρ Y

/-- Corollary 14.14, display (W9): the minimax risk of an exact power law on the
window lies between `10^{-18} min{ρ, Y}` and `3.4·10^5 min{ρ, Y}`. -/
def WindowRiskStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    let Y := 1 / (a * Real.sqrt B) *
      Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ)))
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ Y) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (340000 * min ρ Y)

/-- Corollary 14.14, the `Ψ` statement: `min{ρ, Y⁰}/√2 ≤ Ψ ≤ 5.13 min{ρ, Y⁰}`
with `Y⁰ = x √(ρ Φ_α(ρ))`. -/
def WindowPsiStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    let Y₀ := 1 / (a * Real.sqrt B) * Real.sqrt (ρ * powerPhi α ρ)
    ENNReal.ofReal (min ρ Y₀ / Real.sqrt 2) ≤ rarePsi μ ρ (1 / Real.sqrt B) ∧
    rarePsi μ ρ (1 / Real.sqrt B) ≤ ENNReal.ofReal (513/100 * min ρ Y₀)

/-- Corollary 14.14, last sentence: when `Y ≤ ρ`, the ratio of the minimax risk to
`Ψ` lies between universal multiples of `√(1 + log N_α(ρ))`. -/
def WindowRatioStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    1 / (a * Real.sqrt B) *
      Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤ ρ →
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 19 * Real.sqrt (1 + Real.log (effectiveScales α ρ))) *
        rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤
      ENNReal.ofReal (500000 * Real.sqrt (1 + Real.log (effectiveScales α ρ))) *
        rarePsi μ ρ (1 / Real.sqrt B)

/-- Remark 14.15, first sentence: at `α = 2` and `a = 1/4`, `Φ_2(ρ) = log(1/ρ)`,
`N_2(ρ) = 1 + log₂(1/ρ)/2`, and the window rate `Y` lies between twice and four
times `√(ρ L H / B)`, the rate of the critical quadratic law. -/
def QuadraticWindowStatement : Prop :=
  ∀ (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    powerPhi 2 ρ = Real.log (1/ρ) ∧
    effectiveScales 2 ρ = 1 + Real.logb 2 (1/ρ) / 2 ∧
    2 * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B) ≤
      1 / ((1/4) * Real.sqrt B) *
        Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ∧
    1 / ((1/4) * Real.sqrt B) *
        Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ≤
      4 * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B)

/-- The consequence of the first sentence of Remark 14.15 for the minimax risk of
the quadratic law `F(d) = (4d)^2`, with explicit constants. -/
def QuadraticRiskStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ 2 (1/4) →
    let C := Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ C) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (1360000 * min ρ C)

/-- Remark 14.15, away from two: once `u = |1 - 2/α| log(1/ρ) ≥ 1`,
`N_α(ρ) = 1/|α - 2|`. -/
def AwayScalesStatement : Prop :=
  ∀ (α ρ : ℝ), 3/2 ≤ α → α ≤ 3 → α ≠ 2 → 0 < ρ → ρ ≤ 1/4 →
    1 ≤ |1 - 2/α| * Real.log (1/ρ) →
    effectiveScales α ρ = 1 / |α - 2|

/-- Remark 14.15, away from two: `Φ_α(ρ)` lies between `1 - e^{-1}` and `1` times
`α/(α - 2)` for `α > 2`, and times `α ρ^{1-2/α}/(2 - α)` for `α < 2`. -/
def AwayPhiStatement : Prop :=
  ∀ (α ρ : ℝ), 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 →
    1 ≤ |1 - 2/α| * Real.log (1/ρ) →
    (2 < α → (1 - Real.exp (-1)) * (α / (α - 2)) ≤ powerPhi α ρ ∧
      powerPhi α ρ ≤ α / (α - 2)) ∧
    (α < 2 → (1 - Real.exp (-1)) * (α * ρ ^ (1 - 2/α) / (2 - α)) ≤ powerPhi α ρ ∧
      powerPhi α ρ ≤ α * ρ ^ (1 - 2/α) / (2 - α))

/-- Remark 14.15, away from two: with `ε = |α - 2|`, the minimax risk is within
universal factors of `min{ρ, x ρ^{min(1/2, 1-1/α)} √((1 + log(1/ε))/ε)}`. -/
def AwayRiskStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → α ≠ 2 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ExactPowerLaw μ α a → 1 ≤ |1 - 2/α| * Real.log (1/ρ) →
    let Z := 1 / (a * Real.sqrt B) * ρ ^ (min (1/2) (1 - 1/α)) *
      Real.sqrt ((1 + Real.log (1 / |α - 2|)) / |α - 2|)
    ENNReal.ofReal (5 * (10 : ℝ)⁻¹ ^ 19 * min ρ Z) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (700000 * min ρ Z)

/-- Remark 14.15, near two: once `|α - 2| log(1/ρ) ≤ 1`, both `Φ_α(ρ)` and
`N_α(ρ)` are of order `log(1/ρ)`, as for the quadratic law. -/
def NearTwoStatement : Prop :=
  ∀ (α ρ : ℝ), 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 →
    |α - 2| * Real.log (1/ρ) ≤ 1 →
    Real.log (1/ρ) / 2 ≤ powerPhi α ρ ∧ powerPhi α ρ ≤ 2 * Real.log (1/ρ) ∧
    Real.log (1/ρ) / 3 ≤ effectiveScales α ρ ∧ effectiveScales α ρ ≤ 2 * Real.log (1/ρ)

end ThresholdHC.CriticalWindow
