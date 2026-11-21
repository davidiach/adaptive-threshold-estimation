import ThresholdHC.QuantileOptimality.Specification

/-! Upper end of the decimal bracket for the optimal quantile factor.

Source: `paper/v6/appendix-optimal-factor.tex`, `thm:sharp-quantile-factor`
(statement at the head of the appendix; the rational certificate for the upper
endpoint in the paragraph `Rational certification`), and
`docs/OPTIMAL_QUANTILE_FACTOR.md`. The theorem states that exactly one
`k ∈ [√2,31/20]` satisfies `max_{1≤u≤31/20} F(k,u) = 1`, that it equals the
sharp factor `c_*` for general laws and for finite laws, and that
`1.462554551279 < c_* < 1.462554551280`.

Here `F(k,u)` is `ThresholdHC.OptimalQuantile.partitionSeries k u`, its maximum
over `[1,31/20]` is `scalarPeak k`, and the root is `scalarRoot`. The sharp factor
`c_*` is represented, as in `ThresholdHC.QuantileOptimality`, as the least `k`
with `Q ≤ k K` over all positive-gap laws (`UniversalFactor`) and over finite
laws (`FiniteUniversalFactor`), for `0 < ρ ≤ 1/4` and `B > 0`. -/
noncomputable section
open Real
namespace ThresholdHC.QuantileFactorUpper
open ThresholdHC.OptimalQuantile ThresholdHC.QuantileOptimality

/-- The scalar peak at `k = 1.462554551280` lies below one. -/
def PeakUpperStatement : Prop :=
  scalarPeak (1462554551280/1000000000000) < 1

/-- The upper end of the bracket: `c_* < 1.462554551280`. -/
def RootUpperStatement : Prop :=
  scalarRoot < (1462554551280/1000000000000 : ℝ)

/-- The decimal bracket `1.462554551279 < c_* < 1.462554551280`. -/
def RootBracketStatement : Prop :=
  (1462554551279/1000000000000 : ℝ) < scalarRoot ∧
    scalarRoot < (1462554551280/1000000000000 : ℝ)

/-- `thm:sharp-quantile-factor` in full: exactly one `k ∈ [√2,31/20]` has
`max_{u∈[1,31/20]} F(k,u) = 1`; it is the least comparison factor for general
laws and for finite laws; and it lies strictly inside the decimal bracket. -/
def SharpQuantileFactorStatement : Prop :=
  ∃ c : ℝ, c ∈ Set.Icc (sqrt 2) (31/20) ∧
    IsGreatest (partitionSeries c '' Set.Icc 1 (31/20)) 1 ∧
    (∀ k ∈ Set.Icc (sqrt 2) (31/20),
      IsGreatest (partitionSeries k '' Set.Icc 1 (31/20)) 1 → k = c) ∧
    (∀ k : ℝ, (UniversalFactor k ↔ c ≤ k) ∧ (FiniteUniversalFactor k ↔ c ≤ k)) ∧
    (1462554551279/1000000000000 : ℝ) < c ∧ c < 1462554551280/1000000000000

end ThresholdHC.QuantileFactorUpper
