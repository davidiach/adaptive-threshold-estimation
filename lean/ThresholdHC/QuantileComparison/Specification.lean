import Mathlib.Analysis.Real.Sqrt

/-! Target type for the scalar inequality of Lemma 3 in the certified-selection
research package (`research/2026-10-30-certified-selection/NOTE.md`). It is the
algebraic step of that package's comparison `K ≤ Q ≤ (8/5) K`. Only this
scalar inequality is a target; the comparison itself, the entropy interaction
bound (Lemma 1) and the scale-separated cost bound (Lemma 2) are not. -/
namespace ThresholdHC.QuantileComparison

/-- Lemma 3: for `T, v, c ≥ 0`,
`T + √(v² + 2Tc + 2v√(Tc)) ≤ (8/5)(√(T² + v²) + c)`. -/
def ScalarComparisonStatement : Prop :=
  ∀ T v c : ℝ, 0 ≤ T → 0 ≤ v → 0 ≤ c →
    T + Real.sqrt (v ^ 2 + 2 * T * c + 2 * v * Real.sqrt (T * c)) ≤
      8 / 5 * (Real.sqrt (T ^ 2 + v ^ 2) + c)

end ThresholdHC.QuantileComparison
