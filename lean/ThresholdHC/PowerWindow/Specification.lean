import ThresholdHC.PsiGap.Specification
import ThresholdHC.ConfidenceEntropy.Full
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The uniform power-law targets of v6 Lemma 14.12 and Theorem 14.13.
The critical-window corollary and its asymptotic reading are separate paper
remarks. The law hypothesis is its exact CDF, with no density supplied as
an additional assumption. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile ThresholdHC.PsiGap

def powerQuantileScale (α ρ : ℝ) : ℝ := ρ ^ (1 / α)

def powerPhi (α ρ : ℝ) : ℝ :=
  α * ∫ s in powerQuantileScale α ρ..1, s ^ (α - 3)

/-- The convention `1/0 = infinity` in (W5) is represented by its explicit
branch at exponent two; no real division-by-zero convention is used. -/
def effectiveScales (α ρ : ℝ) : ℝ :=
  if α = 2 then 1 + Real.logb 2 (1 / ρ) / 2
  else min (1 + Real.logb 2 (1 / ρ) / α) (max 1 (1 / |α - 2|))

def powerTail (α x ρ : ℝ) : ℝ :=
  x ^ α + α * x * ∫ s in x..powerQuantileScale α ρ, s ^ (α - 2)

def uniformRate (α x ρ : ℝ) : ℝ :=
  if x < powerQuantileScale α ρ then
    min ρ (powerTail α x ρ + x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))))
  else ρ

def PowerPhiStatement : Prop :=
  ∀ (α ρ : ℝ), 0 < α → 0 < ρ → ρ < 1 →
    powerPhi α ρ = if α = 2 then Real.log (1 / ρ)
      else α * (1 - ρ ^ (1 - 2 / α)) / (α - 2)

def PowerCoreStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ < 1 → ExactPowerLaw μ α a →
    a^2 * coreCost μ ρ = powerPhi α ρ ∧
    (1/2 : ℝ) * (1 + Real.log (effectiveScales α ρ)) ≤ 1 + coreEntropy μ ρ ∧
    1 + coreEntropy μ ρ ≤ (383/100 : ℝ) * (1 + Real.log (effectiveScales α ρ))

def PowerQuantileStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ)

def PowerRiskStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) ≤
      rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (60002 * uniformRate α (1 / (a * Real.sqrt B)) ρ)

def PowerConfidenceStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B δ : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    0 < δ → δ ≤ 1/4 → ExactPowerLaw μ α a →
    let x := Real.sqrt (Real.log (1 / δ) / B) / a
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α x ρ) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ≤
      ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤
      ENNReal.ofReal (1500000 * uniformRate α x ρ)

end ThresholdHC.PowerWindow
