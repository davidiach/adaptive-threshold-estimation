import ThresholdHC.CapIdentification.PolynomialL2
import ThresholdHC.CapIdentification.DiameterAttainment

/-! Target statement for the explicit lower estimate that follows Theorem
`thm:cap-identifiability` (paper/v6/appendix-identifiability.tex, the proof's
last paragraph and the display after it; the same text is in
paper/rare-event/v2/sections/identifiability.tex).

With `L = ⌈N/2⌉ = (N+1)/2`, `V_L = span{d, d³, …, d^(2L-1)} ⊂ L²(μ)`
(`oddL2Span μ L`) and `h = 1 - proj_{V_L} 1`, where `1` is the L²(μ) class
`polynomialL2 μ 1` of the constant function: if `1 ∉ V_L`, then `h` is a
nonzero class with finite `L^∞(μ)` norm (essentially bounded), orthogonal to
every odd monomial `d^(2j+1)` with
`j < L`, with `∫ h dμ = ∫ h² dμ = ‖h‖²_{L²(μ)} > 0`, and
`Δ_N/2 ≥ ρ‖h‖²_{L²(μ)} / (4‖h‖_{L^∞(μ)})`, where `Δ_N` is the attained
moment-matching diameter `capDiameter μ ρ N` over globally rare sign laws.
The paper's standing range is `0 < ρ ≤ 1/2` and `N ≥ 1`; the statement allows
`0 < ρ ≤ 1` and every `N`. The proof is in `Estimate.lean`. -/

noncomputable section
namespace ThresholdHC.CapIdentificationEstimate
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.CapIdentification (polynomialL2 oddL2Span capDiameter)

/-- Explicit fixed-cap lower estimate. For a probability law `μ` of gaps,
`0 < ρ ≤ 1`, a cap `N`, and `L = (N+1)/2`, suppose the constant `1` is not in
the odd-monomial span `V_L ⊂ L²(μ)`. Let `h = 1 - proj_{V_L} 1`. Then `h ≠ 0`,
its `L^∞(μ)` norm is finite and strictly positive, `h` is orthogonal to
`d^(2j+1)` for every `j < L`, `∫ h dμ = ∫ h² dμ`, this common value is
strictly positive and equals `‖h‖²_{L²(μ)}`, and
`ρ‖h‖²_{L²(μ)} / (4‖h‖_{L^∞(μ)}) ≤ Δ_N/2`. -/
def ExplicitCapEstimateStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ N : ℕ,
    polynomialL2 μ 1 ∉ oddL2Span μ ((N+1)/2) →
    let h : Lp ℝ 2 μ := polynomialL2 μ 1 -
      (oddL2Span μ ((N+1)/2)).starProjection (polynomialL2 μ 1)
    h ≠ 0 ∧ eLpNorm (⇑h) ∞ μ ≠ ∞ ∧ 0 < (eLpNorm (⇑h) ∞ μ).toReal ∧
      (∀ j : Fin ((N+1)/2), ∫ d, h d * (d : ℝ) ^ (2*j.val+1) ∂μ = 0) ∧
      (∫ d, h d ∂μ) = ∫ d, (h d) ^ 2 ∂μ ∧
      0 < ∫ d, (h d) ^ 2 ∂μ ∧
      ‖h‖ ^ 2 = ∫ d, (h d) ^ 2 ∂μ ∧
      ρ * ‖h‖ ^ 2 / (4 * (eLpNorm (⇑h) ∞ μ).toReal) ≤ capDiameter μ ρ N / 2

end ThresholdHC.CapIdentificationEstimate
