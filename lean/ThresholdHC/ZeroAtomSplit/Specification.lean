import ThresholdHC.ArbitraryLawAdaptation.ZeroQuantile

/-! Target statements for the zero-atom split of the selection functional,
the identity used in results/arbitrary-law-zero-quantile-20261112/README.md
(numerical check): for `α = z δ₀ + (1 - z) η`, with `η` a probability law of
positive gaps,

  `K_α(B) = min{ρ, z + (1 - z) K_{η, ρ/(1 - z)}(B)}`.

The positive part is taken at the rarity `ρ/(1 - z)`, not at the design rarity
`(ρ - z)/(1 - z)` of the quantile design. The proof is in `Support.lean`. -/
noncomputable section
namespace ThresholdHC.ZeroAtomSplit
open MeasureTheory ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

/-- For a probability law `η` of positive gaps, a zero mass `0 ≤ z < 1`, a rarity
`ρ > 0` and a budget `B > 0`, the selection functional of `z δ₀ + (1 - z) η` is
`K_{zδ₀+(1-z)η,ρ}(B) = min{ρ, z + (1 - z) K_{η,ρ/(1-z)}(B)}`. -/
def ZeroAtomSplitStatement : Prop :=
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] (z ρ B : ℝ),
    0 ≤ z → z < 1 → 0 < ρ → 0 < B →
    zeroSelection (zeroAtomLaw z η) ρ B =
      min (ENNReal.ofReal ρ)
        (ENNReal.ofReal z + ENNReal.ofReal (1 - z) * selection η (ρ / (1 - z)) B)

/-- The same split for every probability law `α` on `[0, 1/2]` with `α{0} < 1`,
with `z = α{0}` and `η` its normalized positive part, for a rarity `ρ > 0` and a
budget `B > 0`. -/
def ZeroAtomSplitLawStatement : Prop :=
  ∀ (α : Measure ℝ) [IsProbabilityMeasure α] (ρ B : ℝ),
    α (Set.Icc 0 (1 / 2))ᶜ = 0 → zeroMass α < 1 → 0 < ρ → 0 < B →
    zeroSelection α ρ B =
      min (ENNReal.ofReal ρ)
        (ENNReal.ofReal (zeroMass α) +
          ENNReal.ofReal (1 - zeroMass α) *
            selection (positiveLaw α) (ρ / (1 - zeroMass α)) B)

end ThresholdHC.ZeroAtomSplit
