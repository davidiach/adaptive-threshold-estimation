import ThresholdHC.CriticalPsi.Model
import ThresholdHC.CriticalEntropy.CriticalMinimax

noncomputable section
namespace ThresholdHC.CriticalPsi
open MeasureTheory ThresholdHC.CriticalEntropy

/-- Exact attained variational formula for the fixed quadratic gap law. -/
def CriticalPsiFormulaStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∃ t : ℝ, 0 < t ∧ t < 1/4 ∧
      ρ = 16*t^2*(1+2*Real.log (1/(4*t))) ∧
      ∀ h : ℝ, 0 < h → criticalPsi ρ h =
        if h < t then 16*(2*h*t*(1+Real.log (1/(4*t)))-h^2) else ρ

/-- Two-sided comparison for the actual supremum, including saturation. -/
def CriticalPsiRateStatement : Prop :=
  ∀ ρ h : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < h →
    min ρ (h*Real.sqrt (ρ*(1+Real.log (1/ρ)))) ≤ criticalPsi ρ h ∧
      criticalPsi ρ h ≤ 16*min ρ (h*Real.sqrt (ρ*(1+Real.log (1/ρ))))

/-- No finite universal multiple of the actual variational objective bounds
the original unrestricted critical minimax risk, even with known law and rarity. -/
def CriticalPsiSeparationStatement : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ ρ : unitInterval, 0 < (ρ : ℝ) ∧ (ρ : ℝ) ≤ 1/4 ∧
      ∃ B : ℝ, 1 ≤ B ∧
        ENNReal.ofReal (C*criticalPsi (ρ : ℝ) (1/Real.sqrt B)) <
          criticalMinimaxRisk (ρ : ℝ) B

end ThresholdHC.CriticalPsi
