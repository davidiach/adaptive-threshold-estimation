import ThresholdHC.PsiGap.Specification

/-! The remaining sharpness and occupied-band conclusions of v6
Proposition 14.9 and Theorem 14.11. These targets extend, rather than alter,
the specifications checked by `PsiClosedForm` and `PsiGap`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiSharpness
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile

/-- The actual number of nonzero band costs in the quantile core. -/
def occupiedBandCount (μ : Measure Gap) (ρ : ℝ) : ℕ :=
  (Function.support (bandCost (quantileCore μ ρ))).ncard

/-- The entropy bound using the occupied bands, including finiteness and
nonemptiness of that support. -/
def OccupiedBandEntropyStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ → ρ ≤ 1/4 →
    (Function.support (bandCost (quantileCore μ ρ))).Finite ∧
    0 < occupiedBandCount μ ρ ∧
    ThresholdHC.PsiGap.coreEntropy μ ρ ≤ Real.log (occupiedBandCount μ ρ) ∧
    Real.log (occupiedBandCount μ ρ) ≤
      Real.log (Real.logb 2 (1 / quantileThreshold μ ρ))

/-- Both the modulus and the entropy-free quantile value on the sharp
two-atom probability law, at every budget with `B⁻¹ᐟ² ≤ d₁/2`. -/
def TwoAtomSharpnessStatement : Prop :=
  ∀ (ρ B : ℝ) (d₁ d₂ : Gap), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    (d₂ : ℝ) = (d₁ : ℝ) * Real.sqrt ((1 - ρ) / ρ) →
    1 / Real.sqrt B ≤ (d₁ : ℝ) / 2 →
    let μ := ENNReal.ofReal ρ • Measure.dirac d₁ +
      ENNReal.ofReal (1 - ρ) • Measure.dirac d₂
    rarePsi μ ρ (1 / Real.sqrt B) =
      ENNReal.ofReal (Real.sqrt 2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) ∧
    quantileZero μ ρ B = ENNReal.ofReal (2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) ∧
    quantileZero μ ρ B = ENNReal.ofReal (Real.sqrt 2) * rarePsi μ ρ (1 / Real.sqrt B)

end ThresholdHC.PsiSharpness
