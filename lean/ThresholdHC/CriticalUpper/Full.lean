import ThresholdHC.CriticalUpper.Budget
import ThresholdHC.CriticalUpper.Specification

/-! The full critical algorithmic and minimax upper bounds against their frozen statements. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem criticalBudget_uniformBudget (ρ : ℝ) (hρ : 0 < ρ) (hρh : ρ ≤ 1/2) (B : ℝ) :
    CriticalUniformBudget (criticalBudgetEstimator ρ B) ρ B := by
  by_cases hlarge : criticalWorkScale ρ/ρ ≤ B
  · rw [criticalBudgetEstimator,ite_eq_left hlarge]
    intro q hq hmass
    exact (fixed_expectedWork_bound ρ hρ (by linarith) q hq hmass (criticalBatchIndex ρ B)).trans
      (ENNReal.ofReal_le_ofReal (criticalBatchIndex_bounds ρ B hρ hρh hlarge).1)
  · rw [criticalBudgetEstimator,ite_eq_right hlarge]
    intro q hq _
    rw [idleCritical_work]
    exact bot_le

theorem criticalBudget_maximalRMSRisk (ρ : ℝ) (hρ : 0 < ρ) (hρh : ρ ≤ 1/2)
    (B : ℝ) (hB : 0 < B) :
    criticalMaximalRMSRisk (criticalBudgetEstimator ρ B) ρ ≤
      ENNReal.ofReal (100000*min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B))) := by
  by_cases hlarge : criticalWorkScale ρ/ρ ≤ B
  · rw [criticalBudgetEstimator,ite_eq_left hlarge,
      min_eq_right (critical_largeBudget_sqrt_le ρ B hρ (by linarith) hlarge)]
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    apply iSup_le
    intro hmass
    have hs := (fixed_squaredRisk_bound ρ hρ (by linarith) q hq hmass (criticalBatchIndex ρ B)).trans
      (ENNReal.ofReal_le_ofReal (critical_largeBudget_square_bound ρ B hρ hρh hlarge))
    have hr := ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 1/2)
    rw [ofReal_square_rpow_half (100000*Real.sqrt (ρ*criticalLogFactor ρ/B)) (by positivity)] at hr
    exact hr
  · rw [criticalBudgetEstimator,ite_eq_right hlarge]
    exact (idleCritical_risk ρ).trans (ENNReal.ofReal_le_ofReal
      (critical_smallBudget_bound ρ B hρ (by linarith) hB (lt_of_not_ge hlarge)))

theorem critical_upper_bound : CriticalUpperStatement := by
  refine ⟨100000,by norm_num,CriticalSeed,inferInstance,
    (fun ρ B => criticalBudgetEstimator (ρ : ℝ) B),?_⟩
  intro ρ hρ hρ' B hB
  exact ⟨criticalBudget_uniformBudget (ρ : ℝ) hρ (by linarith) B,
    criticalBudget_maximalRMSRisk (ρ : ℝ) hρ (by linarith) B (by linarith)⟩

theorem critical_minimax_upper_bound : CriticalMinimaxUpperStatement := by
  refine ⟨100000,by norm_num,?_⟩
  intro ρ hρ hρ' B hB
  apply le_trans ?_ (criticalBudget_maximalRMSRisk (ρ : ℝ) hρ (by linarith) B (by linarith))
  apply sInf_le
  exact ⟨CriticalSeed,inferInstance,criticalBudgetEstimator (ρ : ℝ) B,
    criticalBudget_uniformBudget (ρ : ℝ) hρ (by linarith) B,rfl⟩

end ThresholdHC.CriticalUpper
