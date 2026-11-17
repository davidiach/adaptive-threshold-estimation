import ThresholdHC.PowerWindow.CoreEntropy
import ThresholdHC.PowerWindow.Statistics

/-! The uniform power-law window: actual core entropy, deterministic quantile
comparison, and the resulting RMS and confidence bounds. The critical-window
corollary and its asymptotic interpretation remain separate paper results. -/
noncomputable section
open MeasureTheory
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiGap

theorem power_quantile : PowerQuantileStatement := power_quantile_of_core power_core

theorem power_risk : PowerRiskStatement := power_risk_of_quantile power_quantile

theorem power_confidence : PowerConfidenceStatement := power_confidence_of_quantile power_quantile

theorem quadratic_core_cost (μ : Measure Gap) [IsProbabilityMeasure μ]
    {a ρ : ℝ} (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ExactPowerLaw μ 2 a) : a^2 * coreCost μ ρ = Real.log (1/ρ) := by
  rw [power_core_cost μ (by norm_num : (0 : ℝ) < 2) ha ha2 hρ hρ1 hm,
    power_phi_closed 2 ρ (by norm_num) hρ hρ1,
    ite_eq_left (show (2 : ℝ) = 2 from rfl)]

end ThresholdHC.PowerWindow
