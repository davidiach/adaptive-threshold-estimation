import ThresholdHC.AnytimeLower.Intervals

/-! Target statements for a remark on the time-uniform lower bound
(`docs/RESULTS.md`, time-uniform confidence; display (TU1) of v6
Appendix `appendix-anytime`).

Stopping a time-uniform interval procedure at physical budget `n` gives a
fixed-budget interval, so the fixed-budget confidence coefficient `10^{-17}`
applies at every `n ≥ 1`. With the inflation `Λ_n = log(1/δ) + log log n`,
this gives display (TU1) with coefficient `10^{-22}` at every `n ≥ 2` with
`log log n ≤ (10^{10} - 1) log(1/δ)`: then `Λ_n ≤ 10^{10} log(1/δ)`, and the
selection functional grows at most like the square root of the budget ratio.

The model is the original observable hidden-gap experiment of the
time-uniform lower bound: an estimate at budget `n` sees the private seed and
the first `n` physical observations. The interval statements assume joint
coverage, as the time-uniform theorem does; the proofs use coverage at the one
budget `n`. The components are in `Prefix.lean` and the targets in
`Full.lean`. -/
noncomputable section
namespace ThresholdHC.StoppedTimeUniform
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.AnytimeLower
open scoped ENNReal

/-- The fixed-budget coefficient `10^{-17}` for every estimate formed from the
seed and the first `n` physical observations of an adaptive population
experiment, under uniform confidence at radius `ε` and level `δ`. -/
def PrefixConfidenceStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ ε : ℝ) (n : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 → 0 ≤ ε → 0 < n →
    ∀ (A : AdaptiveEstimator R) (H : R × Prefix n → ℝ), Measurable H →
      (∀ q : SignLaw, RarePrior μ ρ q →
        (observablePrefixLaw μ A q n) {x | ε < |H x - signMean μ q.val|} ≤ ENNReal.ofReal δ) →
      ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) *
          ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / Real.log (1/δ)) ≤ ENNReal.ofReal ε

/-- Every time-uniform interval procedure with joint coverage and half-width
envelope `t` satisfies the fixed-budget bound at every budget `n ≥ 1`. -/
def StoppedFixedBudgetStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    ∀ (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ n : ℕ, 0 < n →
        (10 : ℝ)⁻¹ ^ 17 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / Real.log (1/δ))).toReal ≤ t n

/-- The remark: display (TU1), with coefficient `10^{-22}`, holds at every
`n ≥ 2` with `log log n ≤ (10^{10} - 1) log(1/δ)`, not only at arbitrarily
late budgets. -/
def StoppedTimeUniformStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    ∀ (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ n : ℕ, 2 ≤ n → Real.log (Real.log (n : ℝ)) ≤ ((10 : ℝ) ^ 10 - 1) * Real.log (1/δ) →
        (10 : ℝ)⁻¹ ^ 22 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal ≤ t n

end ThresholdHC.StoppedTimeUniform
