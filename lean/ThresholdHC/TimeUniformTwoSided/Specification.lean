import ThresholdHC.AnytimeLower.Intervals

/-! Target statements composing the two halves of the time-uniform confidence
result in one model (`docs/RESULTS.md`, section Time-uniform confidence;
`paper/v6/appendix-anytime.tex`, Appendix `app:anytime`: the opening
time-uniform upper theorem and display (TU1) of the theorem
Law-dependent time-uniform lower bound).

The upper theorem `ThresholdHC.Anytime.known_anytime` is stated for a
budget-indexed family of stage controllers under its own stream law, and the
lower theorem `ThresholdHC.AnytimeLower.law_dependent_interval_lower` for one
online policy in the original observable hidden-gap experiment. Here the upper
procedure is restated in the lower theorem's model: one adaptive estimator, a
single private seed, and at every integer budget `n` an interval that reads the
seed and the first `n` physical observations of the actual experiment. Joint
coverage and width control are expressed by
`ThresholdHC.AnytimeLower.OnlineIntervalCoverage`, so validity at a
data-dependent stopping budget follows from the single coverage event.

The upper envelope keeps the source form `1500002 K(n/Λ(n,δ))` at every integer
`n ≥ 1`, with `Λ(n,δ) = log(1/δ) + 2 log(2 + log(1+n)/log 2)` written inline.
On the lower theorem's scale `λ(n) = log(1/δ) + log log n` it is at most
`3000004 K(n/λ(n))` for `n ≥ 3`, because `Λ(n,δ) ≤ 4 λ(n)` there. The source
claims only that the two halves match up to constants; the joint constants
`3000004` and `10^{-22}` are the ones proved here.

Not restated: the nesting of the intervals `I(B)`, real budgets `B ≥ 0` (only
integer budgets appear), and the per-budget pathwise flip cap of the stage
controllers. The cap is replaced by the typing of the interval maps, which at
budget `n` read only the first `n` observations. The constructed policy itself
never stops; neither statement imposes a work or budget hypothesis on the
policy. The proofs are in `Online.lean` and `Scale.lean`, and the targets in
`Full.lean`. -/
noncomputable section
namespace ThresholdHC.TimeUniformTwoSided
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.AnytimeLower

/-- One online policy in the original observable experiment. At integer budget
`n` its interval reads the seed and the first `n` physical observations. It has
joint simultaneous coverage and width control with an envelope at most
`1500002 K(n/Λ(n,δ))` for `n ≥ 1` and at most `3000004 K(n/λ(n))` for `n ≥ 3`. -/
def OnlineUpperStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R)
      (L U : ∀ n, R × Prefix n → ℝ) (t : ℕ → ℝ),
      (∀ n, Measurable (L n)) ∧ (∀ n, Measurable (U n)) ∧ (∀ n, 0 ≤ t n) ∧
      OnlineIntervalCoverage μ A L U ρ δ t ∧
      (∀ n : ℕ, 1 ≤ n → t n ≤ 1500002 *
        (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) /
          (Real.log (1/δ) + 2 * Real.log (2 + Real.log (1 + (n : ℝ)) / Real.log 2)))).toReal) ∧
      (∀ n : ℕ, 3 ≤ n → t n ≤ 3000004 *
        (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal)

/-- Two-sided order in one model. Some online procedure with measurable
endpoints, a nonnegative envelope and joint coverage and width control
(`OnlineIntervalCoverage`) has an envelope at most `3000004 K(n/λ(n))` for
`n ≥ 3` and at least `10^{-22} K(n/λ(n))` at arbitrarily late budgets. Every
procedure with measurable endpoints and a nonnegative envelope satisfying
`OnlineIntervalCoverage` obeys the same lower bound. -/
def TimeUniformTwoSidedStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ ≤ 1/4 →
    (∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R)
        (L U : ∀ n, R × Prefix n → ℝ) (t : ℕ → ℝ),
        (∀ n, Measurable (L n)) ∧ (∀ n, Measurable (U n)) ∧ (∀ n, 0 ≤ t n) ∧
        OnlineIntervalCoverage μ A L U ρ δ t ∧
        (∀ n : ℕ, 3 ≤ n → t n ≤ 3000004 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal) ∧
        (∀ M : ℕ, ∃ n : ℕ, max M 3 ≤ n ∧ (10 : ℝ)⁻¹ ^ 22 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal ≤ t n)) ∧
    (∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ M : ℕ, ∃ n : ℕ, max M 3 ≤ n ∧ (10 : ℝ)⁻¹ ^ 22 *
        (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ) / budgetInflation δ n)).toReal ≤ t n)

end ThresholdHC.TimeUniformTwoSided
