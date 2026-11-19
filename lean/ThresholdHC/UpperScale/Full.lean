import ThresholdHC.UpperScale.Specification
import ThresholdHC.UpperScale.Batch
import ThresholdHC.UpperMixture.Full

/-! The RMS upper bound with the constant 12.

For a budget `B ≥ 4`, let `L` be the level with `4*2^L ≤ B < 8*2^L` and
`t = B/(4*2^L)`, so `1 ≤ t < 2`. The family runs the calibrated batch at level
`L` with calibration scale `t*2^L = B/4` (`scaledEstimator`), which uses the
whole budget `B` (`scaled_uniformBudget`). Below `B = 4` it is the idle
estimator of `BlindUpper`, whose RMS risk is at most one, the value of the
modulus there.

At scale `t*2^L` the mean-square error is at most `(1 + (169/5)/t)*ω_L^2`, with
`ω_L = ω(2^{-L/2})` (`scaled_squaredRisk_le`). Since `2^L*ω_L^2 ≤ B*ω_B^2` with
`ω_B = ω(B^{-1/2})`, `ω_L^2 ≤ 4*t*ω_B^2`, so the mean-square error is at most
`4*(t + 169/5)*ω_B^2 ≤ (716/5)*ω_B^2 ≤ 12^2*ω_B^2`. The two-level mixture of
`UpperMixture` would give `(9/2)*(174/5) = 783/5`, above `12^2`. -/
noncomputable section
namespace ThresholdHC.UpperScale
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.BlindUpper ThresholdHC.UpperMixture
open scoped ENNReal

/-- The ratio of the budget to `4*2^L`, at the level `L` of the budget. -/
def budgetRatio (B : ℝ) : ℝ := B / (4 * (2 : ℝ) ^ (budgetLevel B))

theorem budgetRatio_bounds (B : ℝ) (hB : 4 ≤ B) : 1 ≤ budgetRatio B ∧ budgetRatio B < 2 := by
  obtain ⟨h1, h2⟩ := budgetLevel_bounds B hB
  have hN : 0 < 4 * (2 : ℝ) ^ (budgetLevel B) := by positivity
  unfold budgetRatio
  constructor
  · rw [le_div_iff₀ hN]
    linarith
  · rw [div_lt_iff₀ hN]
    linarith

theorem budgetRatio_budget (B : ℝ) : 4 * (budgetRatio B * (2 : ℝ) ^ (budgetLevel B)) = B := by
  have hN : 0 < (2 : ℝ) ^ (budgetLevel B) := by positivity
  unfold budgetRatio
  field_simp

/-- The distribution-blind family: the calibrated batch at scale `B/4`. -/
def scaledFamily (B : ℝ) : AdaptiveEstimator BatchSeed :=
  if 4 ≤ B then scaledEstimator (budgetLevel B) (budgetRatio B) else idleBatchEstimator

theorem scaledFamily_uniformBudget (B : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    UniformBudget μ (scaledFamily B) B := by
  by_cases hlarge : 4 ≤ B
  · rw [scaledFamily, ite_eq_left hlarge]
    have h := scaled_uniformBudget (budgetLevel B) (budgetRatio B) μ
    have hs : 4 * calScale (budgetLevel B) (budgetRatio B) = B := by
      rw [calScale, scaleRatio_of_one_le (budgetRatio_bounds B hlarge).1]
      exact budgetRatio_budget B
    rwa [hs] at h
  · rw [scaledFamily, ite_eq_right hlarge]
    intro q
    rw [idleBatch_expectedWork_zero]
    exact zero_le

theorem scaledFamily_maximalRMSRisk (B : ℝ) (hB : 1 ≤ B) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (scaledFamily B) ≤ ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B)) := by
  by_cases hlarge : 4 ≤ B
  · rw [scaledFamily, ite_eq_left hlarge]
    obtain ⟨ht1, ht2⟩ := budgetRatio_bounds B hlarge
    set L := budgetLevel B
    set t := budgetRatio B
    set N : ℝ := (2 : ℝ) ^ L
    have hN : 0 < N := by positivity
    have hbud : 4 * (t * N) = B := budgetRatio_budget B
    let w := modulus μ (1 / Real.sqrt B)
    let a := modulus μ (1 / Real.sqrt N)
    have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
    have ha : N * a ^ 2 ≤ B * w ^ 2 := modulus_sq_scale μ hN (by nlinarith)
    have ha' : a ^ 2 ≤ 4 * t * w ^ 2 := by
      rw [← hbud] at ha
      have h : N * a ^ 2 ≤ N * (4 * t * w ^ 2) := by linarith
      exact le_of_mul_le_mul_left h hN
    have ht0 : 0 < t := by linarith
    have hfac : 0 ≤ 1 + (169/5) / t := by positivity
    have hrisk : (1 + (169/5) / t) * a ^ 2 ≤ (12 * w) ^ 2 := by
      have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
      calc
        (1 + (169/5) / t) * a ^ 2 ≤ (1 + (169/5) / t) * (4 * t * w ^ 2) :=
          mul_le_mul_of_nonneg_left ha' hfac
        _ = 4 * (t + 169/5) * w ^ 2 := by field_simp
        _ ≤ 144 * w ^ 2 := by nlinarith
        _ = (12 * w) ^ 2 := by ring
    apply iSup_le
    intro q
    unfold rootMeanRisk
    have hsq : squaredRisk (experimentLaw μ (scaledEstimator L t) q)
        (populationOutput (scaledEstimator L t)) (signMean μ q.val) ≤
        ENNReal.ofReal ((12 * w) ^ 2) :=
      (scaled_squaredRisk_le L ht1 μ q).trans (ENNReal.ofReal_le_ofReal hrisk)
    have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [ofReal_square_rpow_half (12 * w) (by positivity)] at hr
  · rw [scaledFamily, ite_eq_right hlarge, smallBudget_modulus μ B hB (lt_of_not_ge hlarge)]
    exact (idleBatch_maximalRMSRisk μ).trans (by norm_num)

theorem blind_upper_12 : BlindUpper12Statement := by
  refine ⟨BatchSeed, inferInstance, scaledFamily, ?_⟩
  intro B hB μ _
  exact ⟨scaledFamily_uniformBudget B μ, scaledFamily_maximalRMSRisk B hB μ⟩

theorem minimax_upper_12 : MinimaxUpper12Statement := by
  intro μ _ B hB
  apply le_trans ?_ (scaledFamily_maximalRMSRisk B hB μ)
  apply sInf_le
  exact ⟨BatchSeed, inferInstance, scaledFamily B, scaledFamily_uniformBudget B μ, rfl⟩

end ThresholdHC.UpperScale
