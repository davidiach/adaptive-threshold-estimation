import ThresholdHC.AnytimeLower.Intervals
import ThresholdHC.StoppingProgram.PositiveValue

/-!
# Bernoulli-subfamily time-uniform lower bound: specification

Source: `docs/UNKNOWN_LAW_CONFIDENCE.md`, section
*A time-uniform lower bound in the original experiment* (the displayed bound
`t(n) >= sqrt(3(1-delta)rho/64) sqrt(log log n / n)` for infinitely many `n`,
and its proof paragraph restricting to constant sign laws in `[rho/2, rho]`
with the chi-square bound `KL(p||q) <= (p-q)^2/(q(1-q))`). The same claim is
recorded in `docs/SECONDARY_CLAIMS.md` (the Bernoulli-subfamily lower bound,
kept paper-only there) and in `paper/v6/verification.tex`, section
`sec:verification` (the paragraph on the earlier unknown-law note's lower
bound for nonincreasing half-width envelopes).

Two statements are fixed here.

* `ConstantPriorPrefixKLStatement`: in the actual hidden-gap online
  experiment, for every adaptive controller (with its private seed law, the
  seed being part of the observation) and every gap law, the observable prefix
  laws of two constant sign laws `theta'` and `theta` differ in KL by at most
  `n (theta'-theta)^2/(theta(1-theta))` after `n` physical observations.
* `BernoulliTimeUniformLowerStatement`: if a deterministic envelope `t`
  bounds the half-width of an online interval on a joint event of
  simultaneous coverage and width with probability at least `1-delta` for
  every sign law of mean at most `rho`, then for every `M` some
  `n >= max M 3` satisfies the displayed bound.

Deviations from the source: the envelope need not be nonincreasing (so the
statement is stronger on that point); the range `0 < delta < 1` is explicit;
infinitely many `n` is formalised as `forall M, exists n >= max M 3`.
-/

noncomputable section
namespace ThresholdHC.BernoulliTimeUniform
open MeasureTheory InformationTheory ThresholdHC.Tier3 ThresholdHC.Tier6
  ThresholdHC.RareAboveTwo ThresholdHC.AnytimeLower
open scoped ENNReal

/-- Two constant sign laws: the observable prefix law (the private seed and the
first `n` physical flips) carries at most `n` chi-square units, for every
controller, with its private seed law, and every gap law. -/
def ConstantPriorPrefixKLStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (θ θ' : ℝ) (hθ : 0 < θ ∧ θ < 1) (hθ' : 0 < θ' ∧ θ' < 1) (n : ℕ),
    klDiv (observablePrefixLaw μ A
        (ThresholdHC.StoppingProgram.constantPrior θ' ⟨hθ'.1.le, hθ'.2.le⟩) n)
      (observablePrefixLaw μ A
        (ThresholdHC.StoppingProgram.constantPrior θ ⟨hθ.1.le, hθ.2.le⟩) n) ≤
      ENNReal.ofReal ((n:ℝ) * (θ' - θ)^2 / (θ * (1 - θ)))

/-- The Bernoulli-subfamily time-uniform lower bound, without monotonicity
of the envelope. -/
def BernoulliTimeUniformLowerStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ < 1 →
    ∀ (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ M : ℕ, ∃ n : ℕ, max M 3 ≤ n ∧
        Real.sqrt (3*(1-δ)*ρ/64) * Real.sqrt (Real.log (Real.log (n:ℝ)) / (n:ℝ)) ≤ t n

end ThresholdHC.BernoulliTimeUniform
