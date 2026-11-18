import ThresholdHC.UpperWork.Specification
import ThresholdHC.UpperWork.Batch
import ThresholdHC.UpperConstant.Full

/-! The distribution-blind estimator of `BlindUpper` attains the RMS upper
bound with the constant 45. The calibrated batch at level `L` has RMS risk at
most `(397/25)*modulus μ (2^{-L/2})`, since `6304/25 ≤ (397/25)^2`. As in
`UpperConstant.Full`, the budget is compared by the factor `17/6`, and
`(397/25)*(17/6) = 6749/150 ≤ 45`. -/
noncomputable section
namespace ThresholdHC.UpperWork
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.BlindUpper
open scoped ENNReal

theorem batch_maximalRMSRisk_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (batchEstimator L) ≤
      ENNReal.ofReal ((397/25)*modulus μ (1/Real.sqrt ((2 : ℝ)^L))) := by
  apply iSup_le
  intro q
  let w := modulus μ (1/Real.sqrt ((2 : ℝ)^L))
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hsq : squaredRisk (experimentLaw μ (batchEstimator L) q)
      (populationOutput (batchEstimator L)) (signMean μ q.val) ≤
        ENNReal.ofReal (((397/25)*w)^2) := by
    rw [batch_squaredRisk_eq]
    exact (cutoffBatch_mse L μ q).trans (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg w]))
  have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [ofReal_square_rpow_half ((397/25)*w) (by positivity)] at hr
  exact hr

theorem budgetEstimator_maximalRMSRisk (B : ℝ) (hB : 1 ≤ B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (budgetEstimator B) ≤ ENNReal.ofReal (45*modulus μ (1/Real.sqrt B)) := by
  by_cases hlarge : 4 ≤ B
  · rw [budgetEstimator,ite_eq_left hlarge]
    have hm : modulus μ (1/Real.sqrt ((2 : ℝ)^(budgetLevel B))) ≤
        (17/6)*modulus μ (1/Real.sqrt B) :=
      (modulus_mono μ (by positivity) (UpperConstant.budgetLevel_scale_sharp B hlarge)).trans
        (UpperConstant.modulus_seventeen_sixths_le μ (by positivity))
    have hw : 0 ≤ modulus μ (1/Real.sqrt B) := modulus_nonneg μ (by positivity)
    exact (batch_maximalRMSRisk_le (budgetLevel B) μ).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  · rw [budgetEstimator,ite_eq_right hlarge,smallBudget_modulus μ B hB (lt_of_not_ge hlarge)]
    exact (idleBatch_maximalRMSRisk μ).trans (by norm_num)

theorem blind_upper_45 : BlindUpper45Statement := by
  refine ⟨BatchSeed,inferInstance,budgetEstimator,?_⟩
  intro B hB μ _
  exact ⟨budgetEstimator_uniformBudget B μ,budgetEstimator_maximalRMSRisk B hB μ⟩

theorem minimax_upper_45 : MinimaxUpper45Statement := by
  intro μ _ B hB
  apply le_trans ?_ (budgetEstimator_maximalRMSRisk B hB μ)
  apply sInf_le
  exact ⟨BatchSeed,inferInstance,budgetEstimator B,budgetEstimator_uniformBudget B μ,rfl⟩

end ThresholdHC.UpperWork
