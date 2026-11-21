import ThresholdHC.Confidence.Specification
import ThresholdHC.RareAboveTwo.Specification

/-! Exact target statements for explicit constants that the guides cite but
that the frozen statements leave existential, or that Lean proved only for
each algorithm.

* Theorem 2.1's coefficient `15/(256√2)` for the confidence radius in the
  hidden model, for each algorithm and for the minimax radius, with the upper
  constant `8192` of the confidence characterization.
* The lower coefficient `1/256` of the rare-event rate for every gap law
  supported below `a`, for each algorithm and for the minimax risk, which the
  frozen `RareSupportedLowerStatement` states as a positive constant.
* The second moment `28ρ` of the observable single-coin estimator, which the
  frozen `RareSingleCoinStatement` states with a positive constant `K`.

The proofs are in `Full.lean`. -/
noncomputable section
namespace ThresholdHC.ExplicitConstants
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.RareAboveTwo
open scoped ENNReal

/-- Every algorithm with uniform expected budget `B ≥ 1` and uniform confidence
radius `r` at level `δ ≤ 1/4` has `r ≥ 15/(256√2) · ω_μ(√(log(1/δ)/B))`. -/
def HiddenConfidenceLowerStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (B δ r : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 → 0 ≤ r →
    UniformBudget μ A B → UniformConfidence μ A r δ →
    (15/(256*Real.sqrt 2)) * modulus μ (confidenceScale B δ) ≤ r

/-- The minimax confidence radius lies between `15/(256√2)` and `8192` times
`ω_μ(√(log(1/δ)/B))`. -/
def HiddenConfidenceMinimaxStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal ((15/(256*Real.sqrt 2)) * modulus μ (confidenceScale B δ)) ≤
        minimaxConfidenceRadius μ B δ ∧
      minimaxConfidenceRadius μ B δ ≤ ENNReal.ofReal (8192 * modulus μ (confidenceScale B δ))

/-- For every gap law supported below `a`, every algorithm with rare budget `B ≥ 1`
has rare-event RMS risk at least `aboveTwoRate a ρ B / 256`. -/
def RareSupportedLower256Statement : Prop :=
  ∀ a ρ B : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], (∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) →
    ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R), RareBudget μ A ρ B →
      ENNReal.ofReal ((1/256) * aboveTwoRate a ρ B) ≤ rareRisk μ A ρ

/-- The same bound for the rare-event minimax risk. -/
def RareSupportedMinimax256Statement : Prop :=
  ∀ a ρ B : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], (∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) →
      ENNReal.ofReal ((1/256) * aboveTwoRate a ρ B) ≤ rareMinimaxRisk μ ρ B

/-- The frozen single-coin statement with `K = 28`: one estimator family that
only ever flips coin `0`, chosen from `a` and `ρ` alone, is, for every `α > 2`,
every `α`-power-margin law and every sign law with `∫ q dμ ≤ ρ`
(`0 < a ≤ 1/2`, `0 < ρ ≤ 1/4`), unbiased with second moment at most `28ρ` and
work at most `W_α/a^2`. -/
def RareSingleCoin28Statement : Prop :=
  ∃ single : ℝ → ℝ → AdaptiveEstimator ℕ,
    (∀ a ρ j xs, (single a ρ).policy j xs = none ∨ (single a ρ).policy j xs = some 0) ∧
    ∀ α : ℝ, 2 < α → ∃ W : ℝ, 0 < W ∧
    ∀ a ρ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], PowerMargin μ α a →
    ∀ q : SignLaw, RarePrior μ ρ q →
      Integrable (populationOutput (single a ρ)) (experimentLaw μ (single a ρ) q) ∧
      (∫ z, populationOutput (single a ρ) z ∂experimentLaw μ (single a ρ) q) = signMean μ q.val ∧
      (∫⁻ z, ENNReal.ofReal ((populationOutput (single a ρ) z)^2)
        ∂experimentLaw μ (single a ρ) q) ≤ ENNReal.ofReal (28*ρ) ∧
      expectedWork μ (single a ρ) q ≤ ENNReal.ofReal (W/a^2)

end ThresholdHC.ExplicitConstants
