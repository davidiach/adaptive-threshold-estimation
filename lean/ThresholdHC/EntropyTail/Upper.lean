import ThresholdHC.EntropyTail.Specification
import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTailExecution.UpperTheorem

/-! The upper half of the entropy–tail law (v6 Theorem 13.3) for the locked
specification. The observable upper bound with constant 28000 is proved in
`ThresholdHC.EntropyTailExecution.UpperTheorem` against the quantile
development's functional; `quantile_selectionValue_le` transfers it to
`selection`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- The observable upper bound `R ≤ 28000 K` for every law, rarity and budget. -/
theorem entropy_tail_upper_explicit (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 28000 * selection μ ρ B :=
  (ThresholdHC.EntropyTailExecution.entropy_tail_upper_28000 μ hρ hρ4 hB).trans
    (mul_le_mul_right (quantile_selectionValue_le μ ρ B) _)

/-- Theorem 13.3: `R ≤ C K` with a universal constant. -/
theorem entropy_tail_upper : EntropyTailUpperStatement := by
  refine ⟨28000, by norm_num, ?_⟩
  intro ρ B hρ hρ4 hB μ _
  exact entropy_tail_upper_explicit μ hρ hρ4 hB

/-- The deterministic comparison `K ≤ Q ≤ (1 + 2√2) K` of the quantile
development, stated for the locked functional `K = selection`. Here `Q` is the
quantile development's closed functional, with a fractional boundary atom. -/
theorem selection_quantile_comparison (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    selection μ ρ B ≤ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧
      ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ≤
        ENNReal.ofReal (1 + 2 * Real.sqrt 2) * selection μ ρ B := by
  rw [← quantile_selectionValue_eq μ ρ B]
  exact ThresholdHC.EntropyTailQuantile.quantile_comparison μ ρ B hρ hρ4 hB

end ThresholdHC.EntropyTail
