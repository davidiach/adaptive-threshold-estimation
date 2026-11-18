import SharpMiddleBudget

open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.SharpRMS

open ThresholdHC.SharpRMS.Window

example : gridChain 16384 endpoints := checked_window

example : ∀ s : ℝ, 2/5 ≤ s → s ≤ 39/40 →
    ∃ hi : ℕ, s ≤ (hi:ℝ)/40960 ∧
      (((hi:ℝ)/40960)/s)^2 * ((upperSum hi:ℝ)/((bins:ℝ)*(scale:ℝ))) ≤ 2/3 := real_window

example : ∀ (g : Gap) (B : ℝ), 2/5 ≤ 2*g.val → 2*g.val ≤ 39/40 →
    (2*g.val)^2*B=4 → ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := middle_minimax_lower

example : ∀ (g : Gap) (B : ℝ), (2*g.val)^2*B=4 →
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := critical_minimax_lower

#print axioms critical_minimax_lower
#print axioms middle_minimax_lower
#print axioms checked_window
#print axioms real_window
