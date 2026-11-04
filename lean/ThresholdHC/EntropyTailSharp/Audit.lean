import ThresholdHC.EntropyTailSharp.Full

/-! Independent statements of the two comparisons, the converse, and the
tail obstruction. In particular, none has a finite-support premise. -/
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailSharp

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal (1 / (10:ℝ)^17) * selection μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ 28000 * selection μ ρ B := by
  simpa only [one_div, inv_pow] using entropy_tail_explicit_law μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal (1 / (10:ℝ)^17) * selection μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ 33000 * selection μ ρ B := by
  simpa only [one_div, inv_pow] using paper_comparison μ hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal (1 / (10:ℝ)^17) * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B := by
  simpa only [one_div, inv_pow] using closed_quantile_lower_explicit μ hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) {S : Type} [MeasurableSpace S]
    (A : AdaptiveEstimator S) (hb : RareBudget μ A ρ B) :
    ENNReal.ofReal (1 / (10:ℝ)^17) * selection μ ρ B ≤ rareRisk μ A ρ := by
  simpa only [one_div, inv_pow] using estimator_entropy_tail_lower μ hρ hρ4 hB A hb

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) (ThresholdHC.EntropyTailQuantile.budgetScale B)/32)
      ≤ rareMinimaxRisk μ ρ B :=
  quantile_tail_lower_general μ hρ hρ4 hB
