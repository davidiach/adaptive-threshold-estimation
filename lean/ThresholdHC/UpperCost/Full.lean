import ThresholdHC.UpperCost.Specification
import ThresholdHC.UpperCost.Batch
import ThresholdHC.UpperMixture.Full

/-! The RMS upper bound with the constant 19.

The calibrated batch at level `L` has mean-square error at most
`K*ω(2^{-L/2})^2` with `K = 401/5` (`Batch`). The family is the budget mixture of
`UpperMixture`, which runs level `L+1` with probability `p = B/(4*2^L) - 1` and
level `L` otherwise, and so uses the whole budget. For any batch factor `K`, its
mean-square error is at most `(9/2)*K*ω(B^{-1/2})^2`
(`budgetMixture_risk_of_batch`), and `(9/2)*(401/5) = 3609/10 ≤ 19^2`. -/
noncomputable section
namespace ThresholdHC.UpperCost
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.BlindUpper ThresholdHC.UpperMixture
open scoped ENNReal

/-- The squared risk of the calibrated batch at level `L`. -/
theorem batch_squaredRisk_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    squaredRisk (experimentLaw μ (batchEstimator L) q) (populationOutput (batchEstimator L))
        (signMean μ q.val) ≤
      ENNReal.ofReal ((401/5) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) := by
  rw [batch_squaredRisk_eq]
  exact cutoffBatch_mse L μ q

/-- The budget mixture turns a batch factor `K` into the RMS constant `c` whenever
`(9/2)*K ≤ c^2` and `1 ≤ c`. -/
theorem budgetMixture_risk_of_batch {K c : ℝ} (hK0 : 0 ≤ K) (hc1 : 1 ≤ c) (hKc : (9/2) * K ≤ c ^ 2)
    (hbatch : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
      squaredRisk (experimentLaw μ (batchEstimator L) q) (populationOutput (batchEstimator L))
          (signMean μ q.val) ≤
        ENNReal.ofReal (K * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2))
    (B : ℝ) (hB : 1 ≤ B) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (budgetMixture B) ≤ ENNReal.ofReal (c * modulus μ (1 / Real.sqrt B)) := by
  have hc0 : 0 ≤ c := by linarith
  by_cases hlarge : 4 ≤ B
  · rw [budgetMixture, ite_eq_left hlarge]
    obtain ⟨hp0, hp1⟩ := levelWeight_bounds B hlarge
    set L := budgetLevel B
    set p := levelWeight B
    set N : ℝ := (2 : ℝ) ^ L
    have hN : 0 < N := by positivity
    have hbud : 4 * N * (1 + p) = B := levelWeight_budget B
    let w := modulus μ (1 / Real.sqrt B)
    let a := modulus μ (1 / Real.sqrt N)
    let b := modulus μ (1 / Real.sqrt ((2 : ℝ) ^ (L + 1)))
    have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
    have ha : N * a ^ 2 ≤ B * w ^ 2 := modulus_sq_scale μ hN (by nlinarith)
    have hb : (2 * N) * b ^ 2 ≤ B * w ^ 2 := by
      have e : (2 : ℝ) ^ (L + 1) = 2 * N := by rw [pow_succ]; ring
      have h := modulus_sq_scale μ (N := (2 : ℝ) ^ (L + 1)) (B := B) (by positivity)
        (by rw [e]; nlinarith)
      rw [← e]
      exact h
    have ha' : a ^ 2 ≤ 4 * (1 + p) * w ^ 2 := by
      rw [← hbud] at ha
      have h4 : 0 < 4 * (1 + p) := by linarith
      nlinarith
    have hb' : b ^ 2 ≤ 2 * (1 + p) * w ^ 2 := by
      rw [← hbud] at hb
      nlinarith
    have hq : (1 + p) * (4 - 2 * p) ≤ 9 / 2 := by nlinarith [sq_nonneg (p - 1 / 2)]
    have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
    have hmix : p * (K * b ^ 2) + (1 - p) * (K * a ^ 2) ≤ (c * w) ^ 2 := by
      calc
        p * (K * b ^ 2) + (1 - p) * (K * a ^ 2) ≤
            p * (K * (2 * (1 + p) * w ^ 2)) + (1 - p) * (K * (4 * (1 + p) * w ^ 2)) := by
          gcongr
        _ = K * w ^ 2 * ((1 + p) * (4 - 2 * p)) := by ring
        _ ≤ K * w ^ 2 * (9 / 2) := mul_le_mul_of_nonneg_left hq (mul_nonneg hK0 hw2)
        _ = ((9 / 2) * K) * w ^ 2 := by ring
        _ ≤ c ^ 2 * w ^ 2 := mul_le_mul_of_nonneg_right hKc hw2
        _ = (c * w) ^ 2 := by ring
    apply iSup_le
    intro q
    unfold rootMeanRisk
    have hsq : squaredRisk (experimentLaw μ (mixEstimator p (batchEstimator L) (batchEstimator (L + 1))) q)
        (populationOutput (mixEstimator p (batchEstimator L) (batchEstimator (L + 1))))
        (signMean μ q.val) ≤ ENNReal.ofReal ((c * w) ^ 2) := by
      rw [mix_squaredRisk p (batchEstimator L) (batchEstimator (L + 1)) (batch_randomLaw_succ L),
        clip_eq hp0 hp1]
      calc
        _ ≤ ENNReal.ofReal p * ENNReal.ofReal (K * b ^ 2) +
            ENNReal.ofReal (1 - p) * ENNReal.ofReal (K * a ^ 2) := by
          gcongr
          · exact hbatch (L + 1) μ q
          · exact hbatch L μ q
        _ = ENNReal.ofReal (p * (K * b ^ 2) + (1 - p) * (K * a ^ 2)) := by
          rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul (by linarith),
            ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) (by positivity))]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hmix
    have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [ofReal_square_rpow_half (c * w) (by positivity)] at hr
  · rw [budgetMixture, ite_eq_right hlarge, smallBudget_modulus μ B hB (lt_of_not_ge hlarge)]
    exact (idleMixture_maximalRMSRisk μ).trans (by simpa using hc1)

theorem budgetMixture_maximalRMSRisk (B : ℝ) (hB : 1 ≤ B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (budgetMixture B) ≤ ENNReal.ofReal (19 * modulus μ (1 / Real.sqrt B)) :=
  budgetMixture_risk_of_batch (K := 401/5) (by norm_num) (by norm_num) (by norm_num)
    (fun L μ _ q => batch_squaredRisk_le L μ q) B hB μ

theorem blind_upper_19 : BlindUpper19Statement := by
  refine ⟨Bool × BatchSeed, inferInstance, budgetMixture, ?_⟩
  intro B hB μ _
  exact ⟨budgetMixture_uniformBudget B μ, budgetMixture_maximalRMSRisk B hB μ⟩

theorem minimax_upper_19 : MinimaxUpper19Statement := by
  intro μ _ B hB
  apply le_trans ?_ (budgetMixture_maximalRMSRisk B hB μ)
  apply sInf_le
  exact ⟨Bool × BatchSeed, inferInstance, budgetMixture B, budgetMixture_uniformBudget B μ, rfl⟩

end ThresholdHC.UpperCost
