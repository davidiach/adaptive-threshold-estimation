import ThresholdHC.PowerWindow.CoreCost

/-! Checked foundation for the uniform power-law window. This module proves
the cost identity, not the entropy bounds or the uniform statistical targets
in Specification. Those remain separate, unproved targets. -/
noncomputable section
open MeasureTheory
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiGap

theorem quadratic_core_cost (μ : Measure Gap) [IsProbabilityMeasure μ]
    {a ρ : ℝ} (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ExactPowerLaw μ 2 a) : a^2 * coreCost μ ρ = Real.log (1/ρ) := by
  rw [power_core_cost μ (by norm_num : (0 : ℝ) < 2) ha ha2 hρ hρ1 hm,
    power_phi_closed 2 ρ (by norm_num) hρ hρ1,
    ite_eq_left (show (2 : ℝ) = 2 from rfl)]

end ThresholdHC.PowerWindow
