import ThresholdHC.BlindUpper.BatchRealization
import ThresholdHC.BlindUpper.BudgetChoice
import ThresholdHC.BlindUpper.Specification

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6
open scoped ENNReal
theorem batch_maximalRMSRisk_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (batchEstimator L) ≤
      ENNReal.ofReal (128*modulus μ (1/Real.sqrt ((2 : ℝ)^L))) := by
  apply iSup_le
  intro q
  let w := modulus μ (1/Real.sqrt ((2 : ℝ)^L))
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hsq : squaredRisk (experimentLaw μ (batchEstimator L) q)
      (populationOutput (batchEstimator L)) (signMean μ q.val) ≤ ENNReal.ofReal ((128*w)^2) :=
    (batch_squaredRisk_le L μ q).trans (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg w]))
  have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [ofReal_square_rpow_half (128*w) (by positivity)] at hr
  exact hr

theorem budgetEstimator_uniformBudget (B : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    UniformBudget μ (budgetEstimator B) B := by
  by_cases hB : 4 ≤ B
  · rw [budgetEstimator,ite_eq_left hB]
    intro q
    exact (batch_uniformBudget (budgetLevel B) μ q).trans
      (ENNReal.ofReal_le_ofReal (budgetLevel_bounds B hB).1)
  · rw [budgetEstimator,ite_eq_right hB]
    intro q
    rw [idleBatch_expectedWork_zero]
    exact bot_le

theorem budgetEstimator_maximalRMSRisk (B : ℝ) (hB : 1 ≤ B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (budgetEstimator B) ≤ ENNReal.ofReal (512*modulus μ (1/Real.sqrt B)) := by
  by_cases hlarge : 4 ≤ B
  · rw [budgetEstimator,ite_eq_left hlarge]
    have hm : modulus μ (1/Real.sqrt ((2 : ℝ)^(budgetLevel B))) ≤
        4*modulus μ (1/Real.sqrt B) :=
      (modulus_mono μ (by positivity) (budgetLevel_scale B hlarge)).trans
        (modulus_quadruple_le μ (by positivity))
    exact (batch_maximalRMSRisk_le (budgetLevel B) μ).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  · rw [budgetEstimator,ite_eq_right hlarge,smallBudget_modulus μ B hB (lt_of_not_ge hlarge)]
    exact (idleBatch_maximalRMSRisk μ).trans (by norm_num)

/-- One observable budget-indexed family, chosen independently of every gap
law, attains the modulus rate in the original experiment. -/
theorem distribution_blind_upper : DistributionBlindUpperStatement := by
  refine ⟨512,by norm_num,BatchSeed,inferInstance,budgetEstimator,?_⟩
  intro B hB μ _
  exact ⟨budgetEstimator_uniformBudget B μ,budgetEstimator_maximalRMSRisk B hB μ⟩

theorem minimax_upper_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hB : 1 ≤ B) :
    minimaxRisk μ B ≤ ENNReal.ofReal (512*modulus μ (1/Real.sqrt B)) := by
  apply le_trans ?_ (budgetEstimator_maximalRMSRisk B hB μ)
  apply sInf_le
  exact ⟨BatchSeed,inferInstance,budgetEstimator B,budgetEstimator_uniformBudget B μ,rfl⟩

end ThresholdHC.BlindUpper
