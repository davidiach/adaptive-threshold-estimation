import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure

/-! Target statements for the optional-stopping counterexample of the
confidence-transfer package,
`research/2026-10-30-confidence-transfer/ANYTIME.md`, section
`Repeatedly inspecting fixed-time intervals is not valid`, displays (28) and
(29); summarized in `docs/RESULTS.md` (confidence-transfer section).

The coin model is the project tape law: the coordinates of `ω : ℕ → Bool` are
iid Bernoulli with success probability `θ`, that is
`Measure.infinitePi (fun _ => bernoulliMeasure true false θ)` (the law
`ThresholdHC.Tier2.tapeMeasure θ`). The head count `H_n` of the first `n`
flips is the number of `t < n` with `ω t = true`.

* (28) for every fixed `n`: `FixedTimeStatement` is the fixed-time coverage of
  the interval centered at `H_n/n` with radius `√(3/(4n))`, uniformly over
  `θ ∈ [0,1/4]`. It is written in the polynomial form `3n < 4(H_n - nθ)²` of
  the miss event `|H_n/n - θ| > √(3/(4n))` for `n ≥ 1`; at `n = 0` the
  polynomial event is empty, so no junk interval enters. At `θ = 1/4` this
  event is the paper's `(4H_n - n)² > 12n`.
* (29): `RepeatedCheckStatement` brackets the probability that the check
  `(4H_n - n)² > 12n` fires at some `n ≤ 512` when `θ = 1/4`. The paper
  displays `0.42809100970105135…`, a floating-point rendering; the exact value
  is `1 - S/4^512` for an integer survivor weight `S`, which equals
  `0.4280910097010513377…`, slightly below the displayed digits. The bracket
  here has 16 correct digits.
* `RepeatedCheckInvalidStatement` puts (28) at `θ = 1/4`, in the paper's
  literal form, next to the conclusion `> 1/4` of (29).

The hidden-coin embedding remarked after (29) (`μ = δ_{1/2}`) is not part of
these statements; they cover the iid Bernoulli(1/4) coin model only. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace ThresholdHC.RepeatedCheck

/-- (28), polynomial form of the miss event of `H_n/n ± √(3/(4n))` (for
`n ≥ 1`; the event is empty at `n = 0`): for every `θ ≤ 1/4` and every fixed
`n` the miss probability is at most `1/4`. -/
def FixedTimeStatement : Prop :=
  ∀ θ : unitInterval, (θ : ℝ) ≤ 1/4 → ∀ n : ℕ,
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
      {ω | 3 * (n : ℝ) < 4 * ((((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n * (θ : ℝ)) ^ 2} ≤ 1/4

/-- (29): at `θ = 1/4`, checking at every `n ≤ 512` against the fixed
reference `1/4` fails with probability `0.4280910097010513377…` (16-digit
bracket, checked against the exact rational `1 - S/4^512`). -/
def RepeatedCheckStatement : Prop :=
  ∀ θ : unitInterval, (θ : ℝ) = 1/4 →
    4280910097010513 / 10^16 < (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧ 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} ∧
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧ 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} < 4280910097010514 / 10^16

/-- (28) and (29) side by side at `θ = 1/4`: every fixed-time check fails with
probability at most `1/4`, the repeated check up to `512` with probability
more than `1/4`. -/
def RepeatedCheckInvalidStatement : Prop :=
  ∀ θ : unitInterval, (θ : ℝ) = 1/4 →
    (∀ n : ℕ, (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} ≤ 1/4) ∧
    1/4 < (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧ 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2}

end ThresholdHC.RepeatedCheck
