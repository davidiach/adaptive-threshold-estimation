import ThresholdHC.FixedPlan.Output

/-! Bias, variance, mean squared error, RMS error and the minimax corollary of the
fixed plan, uniformly over measurable sign laws at an arbitrary gap law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThresholdHC.FixedPlan
open ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailExecution ThresholdHC.BlindUpper

theorem exists_pred_of_pos {n : ℕ} (hn : 0 < n) : ∃ n', n = n'+1 := ⟨n-1, by omega⟩

/-- Exact mean of the plan's output. -/
theorem majority_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ) (hn : 0 < n) :
    (∫ z, populationOutput (majorityEstimator k n) z ∂experimentLaw μ (majorityEstimator k n) q) =
      ∫ d, q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d ∂μ := by
  obtain ⟨n', rfl⟩ := exists_pred_of_pos hn
  rw [majority_output_mean, majorityVote_population_mean]

theorem integrable_signLaw (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw) : Integrable q.val μ :=
  Tier5.integrable_of_abs_bound μ _ q.property.1 1 (fun d => by
    rw [abs_of_nonneg (q.property.2 d).1]
    exact (q.property.2 d).2)

/-- The mixture mean differs from the sign mean by at most `e_m`. -/
theorem mixture_bias (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k : ℕ) :
    |(∫ d, q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d ∂μ) -
      signMean μ q.val| ≤ meanMajorityMiss μ k := by
  have hq := integrable_signLaw μ q
  have hm := integrable_majorityMiss μ k
  have hmm := measurable_majorityMiss k
  have hf : Integrable (fun d => q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d) μ := by
    apply Tier5.integrable_of_abs_bound μ
      (fun d => q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d)
      ((q.property.1.mul (measurable_const.sub hmm)).add ((measurable_const.sub q.property.1).mul hmm)) 1
    intro d
    have hq0 := (q.property.2 d).1
    have hq1 := (q.property.2 d).2
    have hm0 := majorityMiss_nonneg k d
    have hm1 := majorityMiss_le_one k d
    have h1 : q.val d * (1 - majorityMiss k d) ≤ q.val d * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hq0
    have h2 : (1 - q.val d) * majorityMiss k d ≤ (1 - q.val d) * 1 :=
      mul_le_mul_of_nonneg_left hm1 (by linarith)
    have h3 : 0 ≤ q.val d * (1 - majorityMiss k d) := mul_nonneg hq0 (by linarith)
    have h4 : 0 ≤ (1 - q.val d) * majorityMiss k d := mul_nonneg (by linarith) hm0
    rw [abs_le]
    constructor <;> linarith
  unfold signMean meanMajorityMiss
  rw [← integral_sub hf hq]
  refine abs_integral_le_integral_abs.trans (integral_mono (hf.sub hq).abs hm (fun d => ?_))
  have hq0 := (q.property.2 d).1
  have hq1 := (q.property.2 d).2
  have hm0 := majorityMiss_nonneg k d
  dsimp only
  rw [show q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d - q.val d =
      majorityMiss k d * (1 - 2 * q.val d) by ring, abs_mul, abs_of_nonneg hm0]
  exact mul_le_of_le_one_right hm0 (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- The bias is at most the mean misclassification probability. -/
theorem majority_bias (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ) (hn : 0 < n) :
    |(∫ z, populationOutput (majorityEstimator k n) z ∂experimentLaw μ (majorityEstimator k n) q)
      - signMean μ q.val| ≤ meanMajorityMiss μ k := by
  rw [majority_mean μ q k n hn]
  exact mixture_bias μ q k

/-- The variance is at most `1/(4n)`. -/
theorem majority_evariance (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ) (hn : 0 < n) :
    evariance (populationOutput (majorityEstimator k n)) (experimentLaw μ (majorityEstimator k n) q)
      ≤ ENNReal.ofReal (1 / (4 * (n : ℝ))) := by
  obtain ⟨n', rfl⟩ := exists_pred_of_pos hn
  rw [majority_output_evariance]
  apply ENNReal.ofReal_le_ofReal
  have hv := majorityVote_variance_le k (originalPopulationTapeLaw μ q)
  have hp : (0 : ℝ) < (n' : ℝ) + 1 := by positivity
  push_cast
  rw [div_le_iff₀ hp, show 1 / (4 * ((n' : ℝ) + 1)) * ((n' : ℝ) + 1) = 1/4 by field_simp]
  exact hv

/-- The mean squared error is at most `e_m^2 + 1/(4n)`. -/
theorem majority_mse (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ) (hn : 0 < n) :
    squaredRisk (experimentLaw μ (majorityEstimator k n) q) (populationOutput (majorityEstimator k n))
      (signMean μ q.val) ≤ ENNReal.ofReal (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ))) := by
  obtain ⟨n', rfl⟩ := exists_pred_of_pos hn
  rw [majority_output_squaredRisk]
  apply ENNReal.ofReal_le_ofReal
  have hv := majorityVote_variance_le k (originalPopulationTapeLaw μ q)
  have hp : (0 : ℝ) < (n' : ℝ) + 1 := by positivity
  have hb := mixture_bias μ q k
  rw [← majorityVote_population_mean] at hb
  have hsq : ((∫ ω, majorityVote k ω ∂originalPopulationTapeLaw μ q) - signMean μ q.val)^2 ≤
      meanMajorityMiss μ k ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hvn : variance (majorityVote k) (originalPopulationTapeLaw μ q) / ((n' : ℝ)+1) ≤
      1 / (4 * ((n' : ℝ)+1)) := by
    rw [div_le_iff₀ hp, show 1 / (4 * ((n' : ℝ) + 1)) * ((n' : ℝ) + 1) = 1/4 by field_simp]
    exact hv
  push_cast
  linarith

theorem majority_rootMeanRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ)
    (hn : 0 < n) :
    rootMeanRisk (experimentLaw μ (majorityEstimator k n) q) (populationOutput (majorityEstimator k n))
      (signMean μ q.val) ≤ ENNReal.ofReal (Real.sqrt (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ)))) := by
  have hX : 0 ≤ meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ)) := by positivity
  unfold rootMeanRisk
  calc
    _ ≤ ENNReal.ofReal (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ))) ^ (1/2 : ℝ) :=
      ENNReal.rpow_le_rpow (majority_mse μ q k n hn) (by norm_num)
    _ = ENNReal.ofReal ((meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ))) ^ (1/2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg hX (by norm_num)
    _ = _ := by rw [Real.sqrt_eq_rpow]

theorem majority_uniformBudget (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ) (B : ℝ)
    (hB : ((n*(2*k+1) : ℕ) : ℝ) ≤ B) : UniformBudget μ (majorityEstimator k n) B := by
  intro q
  rw [majority_expectedWork, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hB

/-- Uniformly over sign laws: budget `n(2k+1)` and RMS error at most `sqrt(e_m^2+1/(4n))`. -/
theorem majority_rms (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ) (hn : 0 < n) :
    UniformBudget μ (majorityEstimator k n) ((n*(2*k+1) : ℕ) : ℝ) ∧
    maximalRMSRisk μ (majorityEstimator k n) ≤
      ENNReal.ofReal (Real.sqrt (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ)))) :=
  ⟨majority_uniformBudget μ k n _ le_rfl, iSup_le (fun q => majority_rootMeanRisk μ q k n hn)⟩

/-- Minimax corollary at every budget `B ≥ n(2k+1)`. -/
theorem majority_minimax (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ) (B : ℝ) (hn : 0 < n)
    (hB : ((n*(2*k+1) : ℕ) : ℝ) ≤ B) :
    Tier6.minimaxRisk μ B ≤ ENNReal.ofReal (Real.sqrt (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ)))) := by
  unfold Tier6.minimaxRisk
  refine (sInf_le ?_).trans (majority_rms μ k n hn).2
  exact ⟨Unit, inferInstance, majorityEstimator k n, majority_uniformBudget μ k n B hB, rfl⟩

end ThresholdHC.FixedPlan
