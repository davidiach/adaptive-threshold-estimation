import ThresholdHC.ConfidenceTransfer.CriticalModel

/-! Target statements for the RMS bound of the common-pair route at the
quadratic critical law (`docs/MODEL_FIDELITY.md`, "How conditional the result
is"). Write `L = 1 + log(1/ρ)`, so `criticalLogFactor ρ = L(1 + log L)`.

The generic RMS transfer `rms_rate_of_common_pair` turns a common pair
`(b, J)` into `R ≥ min{b, √(J/B)}/128`. Lean proves a common pair for the
critical law, with `b = ρ/32` and `J = a ρ L(1 + log L)` for some `a > 0`
(`critical_common_pair_bound`), but no theorem composed the two. The
composition is in `Full.lean`. The constant `a` is existential and not
explicit, so the bound adds no rate: the critical RMS law is checked with
explicit constants `10^{-18}` and `100000` (`PaperStatements.critical_explicit_constants`,
with `PaperStatements.critical_minimax_eq` identifying the minimax risks) and
with an existential constant (`critical_minimax_lower_bound`). -/
noncomputable section
namespace ThresholdHC.CriticalPairRMS
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open scoped ENNReal

/-- For some `a > 0`, fixed before `ρ`, `B` and the algorithm and not explicit,
every algorithm with rare budget `B` has
`R ≥ min{ρ/32, √(a ρ L(1+log L)/B)}/128` at the critical law. -/
def CriticalPairRMSStatement : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
      RareBudget ThresholdHC.ConfidenceTransfer.criticalPositiveLaw A ρ B →
      ENNReal.ofReal (min (ρ/32)
          (Real.sqrt (a*(ρ*ThresholdHC.CriticalEntropy.criticalLogFactor ρ)/B))/128) ≤
        rareRisk ThresholdHC.ConfidenceTransfer.criticalPositiveLaw A ρ

/-- The same bound for the minimax risk. -/
def CriticalPairMinimaxRMSStatement : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal (min (ρ/32)
        (Real.sqrt (a*(ρ*ThresholdHC.CriticalEntropy.criticalLogFactor ρ)/B))/128) ≤
      rareMinimaxRisk ThresholdHC.ConfidenceTransfer.criticalPositiveLaw ρ B

end ThresholdHC.CriticalPairRMS
