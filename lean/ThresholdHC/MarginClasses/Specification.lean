import ThresholdHC.Confidence.Model
import ThresholdHC.UnbiasedConverse.Model

/-! Target statements for the margin-class corollaries of the v6 manuscript
(`paper/v6/core.tex`, Section `sec:rates`).

* Corollary `cor:gap` (gap classes): for the class `𝒢_Δ` of gap laws with no
  mass below `Δ`, the minimax uniform expected work for `(ε,δ)` accuracy is of
  order `log(1/δ)/(ε^2 Δ^2)`, with universal constants and a universal
  small-accuracy cutoff. Here the constants are `(15/(256√2))^2 = 225/131072`
  and `8192^2 = 67108864`, and the cutoff is `ε ≤ 1/25`.
* Corollary `cor:power` (sharp polynomial-margin complexity), for the class
  `𝒢_{α,C}` of display `eq:power-class`: the rows `0 < α < 1` (order
  `log(1/δ) ε^{-2/α}`) and `α > 1` (order `log(1/δ) ε^{-2}`) of display
  `eq:power-complexity`, with explicit constants and the cutoff `ε ≤ 1/25`;
  the unbiased dichotomy on the whole class (finite uniform variance and work
  if and only if `α > 1`); and one common estimator chosen before `α` and `C`,
  both for unbiased estimation (`α > 1`) and as a single `(B,δ)`-indexed
  confidence family attaining every stated upper budget.

Not covered: the critical row `α = 1` of `eq:power-complexity`, and the
claim in the proof of `cor:power` that the universal estimator is integrable
and unbiased for `α ≤ 1`.

Conventions. A gap law is a probability law of `D = |P - 1/2|` on `(0,1/2]`;
both classes force zero mass at `D = 0`. `(ε,δ)`-validity is
`UniformConfidence`: the strict failure event `ε < |θ̂ - θ|` has probability at
most `δ` under every measurable sign law. `classWork` is the infimum of the
real budgets `B` for which one estimator has `UniformBudget` `B` and is
`(ε,δ)`-valid at every law of the class. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.MarginClasses
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.UnbiasedConverse

/-- Smallest uniform expected-work budget of one estimator that is `(ε,δ)`-valid
(strict failure event, every measurable sign law) at every gap law of the class. -/
def classWork (P : Measure Gap → Prop) (ε δ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (B : ℝ),
    (∀ (ν : Measure Gap) [IsProbabilityMeasure ν], P ν →
      UniformBudget ν A B ∧ UniformConfidence ν A ε δ) ∧ t = ENNReal.ofReal B}

/-- The gap class `𝒢_Δ`: no mass at gaps strictly below `Δ`. -/
def GapClass (Δ : ℝ) (ν : Measure Gap) : Prop := ν {d : Gap | (d : ℝ) < Δ} = 0

/-- The polynomial-margin class `𝒢_{α,C}`: `P(|P-1/2| ≤ t) ≤ C t^α` for `0 < t ≤ 1/2`. -/
def PowerClass (α C : ℝ) (ν : Measure Gap) : Prop :=
  ∀ t : ℝ, 0 < t → t ≤ 1/2 → ν.real {d : Gap | (d : ℝ) ≤ t} ≤ C * t ^ α

/-- Corollary `cor:gap`, with universal constants `(15/(256√2))^2` and `8192^2`
and universal cutoff `1/25`. -/
def GapClassStatement : Prop :=
  ∀ Δ ε δ : ℝ, 0 < Δ → Δ ≤ 1/2 → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (225/131072 * Real.log (1/δ) / (ε^2 * Δ^2)) ≤ classWork (GapClass Δ) ε δ ∧
    classWork (GapClass Δ) ε δ ≤ ENNReal.ofReal (67108864 * Real.log (1/δ) / (ε^2 * Δ^2))

/-- Corollary `cor:power`, row `0 < α < 1`. -/
def SublinearClassStatement : Prop :=
  ∀ α C ε δ : ℝ, 0 < α → α < 1 → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal ((15 * C / (256 * Real.sqrt 2)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α))
        ≤ classWork (PowerClass α C) ε δ ∧
      classWork (PowerClass α C) ε δ ≤
        ENNReal.ofReal ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α))

/-- Corollary `cor:power`, row `α > 1` (the lower constant is universal). -/
def SuperlinearClassStatement : Prop :=
  ∀ α C ε δ : ℝ, 1 < α → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (225/32768 * Real.log (1/δ) / ε^2) ≤ classWork (PowerClass α C) ε δ ∧
      classWork (PowerClass α C) ε δ ≤
        ENNReal.ofReal ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2)

/-- Corollary `cor:power`, the unbiased dichotomy on the whole class: one
estimator is unbiased with finite uniform variance and expected work at every
law of `𝒢_{α,C}` if and only if `α > 1`. -/
def PowerUnbiasedStatement : Prop :=
  ∀ α C : ℝ, 0 < α → 2 ^ α ≤ C →
    ((∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (V W : ℝ), 0 ≤ V ∧ 0 ≤ W ∧
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
        UniformlyUnbiased ν A ∧ UniformVarianceBound ν A V ∧ UniformBudget ν A W) ↔ 1 < α)

/-- Corollary `cor:power`, one common unbiased estimator, chosen before `α`
and `C`, for every `α > 1`. -/
def CommonUnbiasedStatement : Prop :=
  ∃ A : AdaptiveEstimator ℕ, ∀ α C : ℝ, 1 < α → 2 ^ α ≤ C →
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
      UniformlyUnbiased ν A ∧
      UniformVarianceBound ν A (23 * (α * C ^ (1/α) / (α - 1))) ∧
      UniformBudget ν A (31 * (α * C ^ (1/α) / (α - 1)))

/-- Corollaries `cor:gap` and `cor:power`: a single `(B,δ)`-indexed family,
chosen before `Δ`, `α`, `C` and `ε`, attains every stated upper budget. -/
def CommonConfidenceStatement : Prop :=
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → AdaptiveEstimator R),
    (∀ Δ ε δ : ℝ, 0 < Δ → Δ ≤ 1/2 → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], GapClass Δ ν →
        UniformBudget ν (rule (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) δ)
            (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) ∧
        UniformConfidence ν (rule (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) δ) ε δ) ∧
    (∀ α C ε δ : ℝ, 0 < α → α < 1 → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
        UniformBudget ν (rule ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) δ)
            ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) ∧
        UniformConfidence ν
          (rule ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) δ) ε δ) ∧
    (∀ α C ε δ : ℝ, 1 < α → 2 ^ α ≤ C → 0 < ε → ε ≤ 1/25 → 0 < δ → δ ≤ 1/4 →
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerClass α C ν →
        UniformBudget ν (rule ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) δ)
            ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) ∧
        UniformConfidence ν
          (rule ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) δ) ε δ)

end ThresholdHC.MarginClasses
