import ThresholdHC.UpperDisagreement.Specification
import ThresholdHC.UpperDisagreement.Batch
import ThresholdHC.UpperCost.Full

/-! The RMS upper bound with the constant 17.

The calibrated batch at level `L` has mean-square error at most
`K*ω(2^{-L/2})^2` with `K = 637/10` (`Batch`). The family is the budget mixture of
`UpperMixture`, and `UpperCost.budgetMixture_risk_of_batch` turns the batch
factor into the RMS constant: `(9/2)*(637/10) = 5733/20 ≤ 17^2`. -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.BlindUpper ThresholdHC.UpperMixture
open scoped ENNReal

/-- The squared risk of the calibrated batch at level `L`. -/
theorem batch_squaredRisk_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    squaredRisk (experimentLaw μ (batchEstimator L) q) (populationOutput (batchEstimator L))
        (signMean μ q.val) ≤
      ENNReal.ofReal ((637/10) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) := by
  rw [batch_squaredRisk_eq]
  exact cutoffBatch_mse L μ q

theorem budgetMixture_maximalRMSRisk (B : ℝ) (hB : 1 ≤ B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (budgetMixture B) ≤ ENNReal.ofReal (17 * modulus μ (1 / Real.sqrt B)) :=
  UpperCost.budgetMixture_risk_of_batch (K := 637/10) (by norm_num) (by norm_num) (by norm_num)
    (fun L μ _ q => batch_squaredRisk_le L μ q) B hB μ

theorem blind_upper_17 : BlindUpper17Statement := by
  refine ⟨Bool × BatchSeed, inferInstance, budgetMixture, ?_⟩
  intro B hB μ _
  exact ⟨budgetMixture_uniformBudget B μ, budgetMixture_maximalRMSRisk B hB μ⟩

theorem minimax_upper_17 : MinimaxUpper17Statement := by
  intro μ _ B hB
  apply le_trans ?_ (budgetMixture_maximalRMSRisk B hB μ)
  apply sInf_le
  exact ⟨Bool × BatchSeed, inferInstance, budgetMixture B, budgetMixture_uniformBudget B μ, rfl⟩

end ThresholdHC.UpperDisagreement
