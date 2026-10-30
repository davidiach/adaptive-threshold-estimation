import ThresholdHC.RareAboveTwo.Model

/-! The entropy–tail selection functional in the unchanged observable rare-event
experiment. Canonical dyadic bands, inverse-square band costs of a submeasure,
the homogeneous cost entropy and its prefix supremum, the truncated inverse-gap
cost, and the selection over submeasures of the magnitude law. All quantities are
extended nonnegative reals: no density, finite inverse moment or finite full-law
entropy is built in. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Canonical band `I_j = (2^{-(j+2)}, 2^{-(j+1)}]`; the bands partition `(0,1/2]`. -/
def band (j : ℕ) : Set Gap :=
  {d | (1/2 : ℝ)^(j+2) < (d : ℝ) ∧ (d : ℝ) ≤ (1/2 : ℝ)^(j+1)}

/-- Inverse-square cost `a_j(σ) = ∫_{I_j} d^{-2} dσ`. -/
def bandCost (σ : Measure Gap) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ d in band j, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ

/-- Homogeneous cost entropy `G(a) = A + Σ_j a_j log(A/a_j)`, `A = Σ_j a_j`.
With Mathlib's conventions a zero coordinate contributes zero. -/
def costEntropy {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  (∑ j, a j) + ∑ j, a j * Real.log ((∑ i, a i) / a j)

/-- `Γ_σ = sup_J G(a_0(σ),…,a_J(σ))`. A band of infinite cost makes it infinite. -/
def gamma (σ : Measure Gap) : ℝ≥0∞ :=
  ⨆ J : ℕ, if ∀ j : Fin (J+1), bandCost σ j ≠ ∞ then
      ENNReal.ofReal (costEntropy fun j : Fin (J+1) => (bandCost σ j).toReal)
    else ∞

/-- Truncated inverse-gap cost `∫ min{1, h/d} dτ`; for `τ = μ` it is `ω_μ(h)`. -/
def tailCost (τ : Measure Gap) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal (min 1 (h / (d : ℝ))) ∂τ

/-- The objective `h√(ρΓ_σ) + ∫ min{1,h/d} d(μ-σ)` at `h = B^{-1/2}`. -/
def selectionObjective (μ : Measure Gap) (ρ B : ℝ) (σ : Measure Gap) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.sqrt B) * (ENNReal.ofReal ρ * gamma σ) ^ (1/2 : ℝ)
    + tailCost (μ - σ) (1 / Real.sqrt B)

/-- The entropy–tail selection functional `K_{μ,ρ}(B)`. -/
def selection (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ), selectionObjective μ ρ B σ)

end ThresholdHC.EntropyTail
