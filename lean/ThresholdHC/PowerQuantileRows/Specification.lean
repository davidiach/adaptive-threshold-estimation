import ThresholdHC.PowerWindow.Specification
import ThresholdHC.CriticalEntropy.CriticalModel

/-! Target statements for Remark `rem:power-quantile` (Agreement with the closed
quantile form) of `paper/v6/rare-events.tex`, subsection The power-margin regimes,
together with the table of RMS orders stated just before it.

For the exact power law `F(d) = (d/a)^α` on `(0, a]` and `x = (a √B)⁻¹`, the
table gives the rows `min{ρ, x^α}` (`0 < α < 1`), `min{ρ, x[1 + log₊(ρ/x)]}`
(`α = 1`), `min{ρ, ρ^{1-1/α} x}` (`1 < α < 2`), `min{ρ, √(ρ L (1 + log L)/B)}`
(`α = 2`, `a = 1/4`) and `min{ρ, √ρ x}` (`α > 2`). The remark says each row
also follows, with constants depending on `α`, from the comparison of the
minimax risk with the closed quantile functional `Q` for every law
(Corollary `fg:cor:general-laws`).

The rows are written in `x`; the `α = 2` row is `min{ρ, x √(ρ L H)}` for every
scale `a`, and `QuadraticRowFormStatement` identifies it at `a = 1/4` with four
times the table entry inside the minimum. The constants are existential and
depend only on `α`. For `α > 4` the quantile and risk statements rest on a
Lean-only extension of v6 Theorem 14.13, whose paper statement covers
`0 < α ≤ 4`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PowerQuantileRows
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow
open ThresholdHC.EntropyTailQuantile

/-- One row of the power-margin table (v6 §11.3, The power-margin regimes),
saturation included, in
`x = (a √B)⁻¹`. The row formulas are written inline. -/
def powerRow (α x ρ : ℝ) : ℝ :=
  if α < 1 then min ρ (x ^ α)
  else if α = 1 then min ρ (x * (1 + max 0 (Real.log (ρ / x))))
  else if α < 2 then min ρ (ρ ^ (1 - 1/α) * x)
  else if α = 2 then min ρ (x * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ))
  else min ρ (Real.sqrt ρ * x)

/-- Deterministic core of the remark: for each fixed exponent the uniform rate
(W7), which is within the factors `1/√2` and `2` of `Q` for the exact power law
(Theorem 14.13; Lean-only for `α > 4`), lies within `α`-dependent factors of
the table row. -/
def PowerRowRateStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ ρ x : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < x →
      c * powerRow α x ρ ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ C * powerRow α x ρ

/-- The closed quantile functional of an exact power law is within
`α`-dependent factors of the table row. -/
def PowerRowQuantileStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ B : ℝ),
      0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
      ENNReal.ofReal (c * powerRow α (1 / (a * Real.sqrt B)) ρ) ≤ closedQuantileValue μ ρ B ∧
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal (C * powerRow α (1 / (a * Real.sqrt B)) ρ)

/-- Remark `rem:power-quantile`: each row follows from `R ≍ Q`
(Corollary `fg:cor:general-laws`). For `α > 4` this rests on a Lean-only
extension of Theorem 14.13 (paper: `0 < α ≤ 4`). -/
def PowerRowRiskStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ B : ℝ),
      0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
      ENNReal.ofReal (c * powerRow α (1 / (a * Real.sqrt B)) ρ) ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (C * powerRow α (1 / (a * Real.sqrt B)) ρ)

/-- At `a = 1/4` the `α = 2` row is the table entry `min{ρ, √(ρ L H / B)}` with the
term inside the minimum multiplied by `4`. -/
def QuadraticRowFormStatement : Prop :=
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    powerRow 2 (1 / ((1/4) * Real.sqrt B)) ρ =
      min ρ (4 * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B))

end ThresholdHC.PowerQuantileRows
