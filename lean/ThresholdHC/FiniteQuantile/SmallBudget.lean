import ThresholdHC.FiniteQuantile.Specification
import ThresholdHC.StoppingProgram.BernoulliFloor
import ThresholdHC.EntropyTailExecution.UpperTheorem

/-! The label obstruction alone controls the entire quantile value when
the expected budget times the rarity is at most one. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal

namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

theorem small_budget_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hB : 0 < B) (hsmall : B * ρ ≤ 1) :
    ENNReal.ofReal (1 / 16 : ℝ) * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B := by
  have hs : ρ ≤ sqrt (ρ / B) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ hB).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hρ.le]
  have hf := StoppingProgram.bernoulli_label_minimax_floor μ ρ B hρ hρ4 hB
  rw [min_eq_left hs, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)] at hf
  exact (mul_le_mul' le_rfl (min_le_left _ _)).trans hf

theorem small_budget_explicit_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hB : 0 < B) (hsmall : B * ρ ≤ 1) :
    ExplicitBounds μ ρ B := by
  refine ⟨?_, ?_⟩
  · have h := ENNReal.ofReal_le_ofReal (by norm_num : (10 : ℝ)⁻¹ ^ 20 ≤ 1 / 16)
    exact (mul_le_mul' h le_rfl).trans (small_budget_lower μ hρ hρ4 hB hsmall)
  · simpa using EntropyTailExecution.closed_quantile_upper_30001 μ hρ hρ4 hB

end ThresholdHC.FiniteQuantile
