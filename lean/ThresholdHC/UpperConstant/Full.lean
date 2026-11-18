import ThresholdHC.UpperConstant.Specification
import ThresholdHC.UpperConstant.Batch
import ThresholdHC.BlindUpper.Full

/-! The distribution-blind estimator of `BlindUpper` attains the RMS upper
bound with the constant 119 in place of 512. The calibrated batch at level
`L` has RMS risk at most `42*modulus μ (2^{-L/2})`, since
`sqrt(12289/7) < 42`. For `B ≥ 4` the level satisfies `B < 8*2^L`, and
`(17/6)^2 ≥ 8` gives `modulus μ (2^{-L/2}) ≤ (17/6)*modulus μ (B^{-1/2})`;
`42*(17/6) = 119`. -/
noncomputable section
namespace ThresholdHC.UpperConstant
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.BlindUpper
open scoped ENNReal

theorem batch_maximalRMSRisk_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (batchEstimator L) ≤
      ENNReal.ofReal (42*modulus μ (1/Real.sqrt ((2 : ℝ)^L))) := by
  apply iSup_le
  intro q
  let w := modulus μ (1/Real.sqrt ((2 : ℝ)^L))
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hsq : squaredRisk (experimentLaw μ (batchEstimator L) q)
      (populationOutput (batchEstimator L)) (signMean μ q.val) ≤ ENNReal.ofReal ((42*w)^2) := by
    rw [batch_squaredRisk_eq]
    exact (cutoffBatch_mse L μ q).trans (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg w]))
  have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [ofReal_square_rpow_half (42*w) (by positivity)] at hr
  exact hr

theorem modulus_seventeen_sixths_le (μ : Measure Gap) [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 ≤ h) :
    modulus μ ((17/6)*h) ≤ (17/6)*modulus μ h := by
  have ht := modulus_scaling μ (6/17) ((17/6)*h) (by norm_num) (by norm_num) (by positivity)
  have he : (6/17 : ℝ)*((17/6)*h) = h := by ring
  rw [he] at ht
  linarith

theorem budgetLevel_scale_sharp (B : ℝ) (hB : 4 ≤ B) :
    1/Real.sqrt ((2 : ℝ)^(budgetLevel B)) ≤ (17/6)*(1/Real.sqrt B) := by
  have hlt := (budgetLevel_bounds B hB).2
  have hN : 0 < (2 : ℝ)^(budgetLevel B) := by positivity
  have hB0 : 0 < B := by linarith
  have hsN := Real.sqrt_pos.mpr hN
  have hsB := Real.sqrt_pos.mpr hB0
  have hsqrt : Real.sqrt B ≤ (17/6)*Real.sqrt ((2 : ℝ)^(budgetLevel B)) := by
    have he : (17/6 : ℝ)*Real.sqrt ((2 : ℝ)^(budgetLevel B)) =
        Real.sqrt ((289/36)*(2 : ℝ)^(budgetLevel B)) := by
      rw [Real.sqrt_mul (by norm_num), show (289/36 : ℝ) = (17/6)^2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [he]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [mul_one_div, div_le_div_iff₀ hsN hsB]
  linarith

theorem budgetEstimator_maximalRMSRisk (B : ℝ) (hB : 1 ≤ B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (budgetEstimator B) ≤ ENNReal.ofReal (119*modulus μ (1/Real.sqrt B)) := by
  by_cases hlarge : 4 ≤ B
  · rw [budgetEstimator,ite_eq_left hlarge]
    have hm : modulus μ (1/Real.sqrt ((2 : ℝ)^(budgetLevel B))) ≤
        (17/6)*modulus μ (1/Real.sqrt B) :=
      (modulus_mono μ (by positivity) (budgetLevel_scale_sharp B hlarge)).trans
        (modulus_seventeen_sixths_le μ (by positivity))
    exact (batch_maximalRMSRisk_le (budgetLevel B) μ).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  · rw [budgetEstimator,ite_eq_right hlarge,smallBudget_modulus μ B hB (lt_of_not_ge hlarge)]
    exact (idleBatch_maximalRMSRisk μ).trans (by norm_num)

theorem blind_upper_119 : BlindUpper119Statement := by
  refine ⟨BatchSeed,inferInstance,budgetEstimator,?_⟩
  intro B hB μ _
  exact ⟨budgetEstimator_uniformBudget B μ,budgetEstimator_maximalRMSRisk B hB μ⟩

theorem minimax_upper_119 : MinimaxUpper119Statement := by
  intro μ _ B hB
  apply le_trans ?_ (budgetEstimator_maximalRMSRisk B hB μ)
  apply sInf_le
  exact ⟨BatchSeed,inferInstance,budgetEstimator B,budgetEstimator_uniformBudget B μ,rfl⟩

end ThresholdHC.UpperConstant
