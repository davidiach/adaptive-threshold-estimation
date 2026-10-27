import Mathlib

/-!
Arbitrary probability laws of positive gaps at most one half, together with
the clipped inverse-gap hard pair for the minimax lower bound. No inverse
moment, density, atomlessness, or tail condition is imposed on the law.
-/

noncomputable section
open MeasureTheory

namespace ThresholdHC.Tier6

abbrev Gap := {d : ℝ // 0 < d ∧ d ≤ 1/2}

def clippedGap (h : ℝ) (d : Gap) : ℝ := min 1 (h / (d : ℝ))

def modulus (μ : Measure Gap) (h : ℝ) : ℝ := ∫ d, clippedGap h d ∂μ

def hardEta (h : ℝ) (d : Gap) : ℝ := (1/8) * clippedGap h d

def hardPlus (h : ℝ) (d : Gap) : ℝ := 1/2 + hardEta h d

def hardMinus (h : ℝ) (d : Gap) : ℝ := 1/2 - hardEta h d

def signMean (μ : Measure Gap) (q : Gap → ℝ) : ℝ := ∫ d, q d ∂μ

def budgetScale (B : ℝ) : ℝ := 1 / (4 * Real.sqrt B)

def HardPairValidityStatement : Prop :=
  ∀ (h : ℝ), 0 < h →
    Measurable (hardEta h) ∧ Measurable (hardPlus h) ∧ Measurable (hardMinus h) ∧
    ∀ d : Gap,
      (0 ≤ hardEta h d ∧ hardEta h d ≤ 1/8) ∧
      (d : ℝ) * hardEta h d ≤ h/8 ∧
      (0 ≤ hardPlus h d ∧ hardPlus h d ≤ 1) ∧
      (0 ≤ hardMinus h d ∧ hardMinus h d ≤ 1)

def HardPairSeparationStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (h : ℝ), 0 < h →
    signMean μ (hardPlus h) - signMean μ (hardMinus h) = (1/4) * modulus μ h

def ModulusScalingStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (c h : ℝ),
    0 ≤ c → c ≤ 1 → 0 ≤ h → c * modulus μ h ≤ modulus μ (c*h)

def BudgetHardPairStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    0 < budgetScale B ∧ (budgetScale B)^2 * B = 1/16 ∧
      modulus μ (1 / Real.sqrt B) / 16 ≤
        signMean μ (hardPlus (budgetScale B)) - signMean μ (hardMinus (budgetScale B))

end ThresholdHC.Tier6
