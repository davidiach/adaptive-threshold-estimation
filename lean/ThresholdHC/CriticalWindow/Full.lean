import ThresholdHC.CriticalWindow.Specification
import ThresholdHC.CriticalWindow.Remark

/-! Corollary 14.14 and Remark 14.15 of v6 §14.8, as Lean theorems.

The corollary simplifies the uniform power-law rate (W7) on the window
`3/2 ≤ α ≤ 3`: the rate is `min{ρ, Y}` within the factor `5.13`, the minimax
risk satisfies display (W9) with the paper's constants, `Ψ` is `min{ρ, Y⁰}`
within the factors `1/√2` and `5.13`, and when `Y ≤ ρ` the ratio of the risk to
`Ψ` is within universal factors of `√(1 + log N_α(ρ))`. The remark identifies the
quadratic law with the critical theorem's rate and reads off the regimes away
from and near exponent two. -/
noncomputable section
namespace ThresholdHC.CriticalWindow
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow

theorem critical_window_rate : WindowRateStatement := by
  intro α ρ x hα1 hα3 hρ hρ4 hx
  have hα : 0 < α := by linarith
  have hK : 1 ≤ 1 + Real.log (effectiveScales α ρ) := by
    linarith [Real.log_nonneg (effective_scales_ge_one hα hρ (by linarith : ρ < 1))]
  have h := window_rate_bounds hα1 hα3 hρ hρ4 hx hK
  rw [windowRate_entropy] at h
  exact h

theorem critical_window_risk : WindowRiskStatement := by
  intro μ _ α a ρ B hα1 hα3 ha ha2 hρ hρ4 hB hm
  exact risk_bounds μ hα1 hα3 ha ha2 hρ hρ4 hB hm

theorem critical_window_psi : WindowPsiStatement := by
  intro μ _ α a ρ B hα1 hα3 ha ha2 hρ hρ4 hB hm
  exact psi_bounds μ hα1 hα3 ha ha2 hρ hρ4 hB hm

theorem critical_window_ratio : WindowRatioStatement := by
  intro μ _ α a ρ B hα1 hα3 ha ha2 hρ hρ4 hB hm hY
  exact ratio_bounds μ hα1 hα3 ha ha2 hρ hρ4 hB hm hY

theorem window_quadratic_rate : QuadraticWindowStatement := by
  intro ρ B hρ hρ4 hB
  exact quadratic_rate_bounds hρ hρ4 hB

theorem window_quadratic_risk : QuadraticRiskStatement := by
  intro μ _ ρ B hρ hρ4 hB hm
  exact quadratic_risk_bounds μ hρ hρ4 hB hm

theorem window_away_scales : AwayScalesStatement := by
  intro α ρ hα1 hα3 hα2 hρ hρ4 hu
  exact away_scales_eq hα1 hα3 hα2 hρ hρ4 hu

theorem window_away_phi : AwayPhiStatement := by
  intro α ρ hα1 _ hρ hρ4 hu
  exact away_phi_bounds hα1 hρ hρ4 hu

theorem window_away_risk : AwayRiskStatement := by
  intro μ _ α a ρ B hα1 hα3 hα2 ha ha2 hρ hρ4 hB hm hu
  exact away_risk_bounds μ hα1 hα3 hα2 ha ha2 hρ hρ4 hB hm hu

theorem window_near_two : NearTwoStatement := by
  intro α ρ hα1 hα3 hρ hρ4 hε
  exact near_two_bounds hα1 hα3 hρ hρ4 hε

end ThresholdHC.CriticalWindow
