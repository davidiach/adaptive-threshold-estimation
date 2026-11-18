import ThresholdHC.UpperMixture.Specification
import ThresholdHC.UpperMixture.Mixture
import ThresholdHC.UpperMoment.Full

/-! The RMS upper bound with the constant 27.

The calibrated batch at level `L` costs at most `4*2^L` and has mean-square
error at most `K*ω(2^{-L/2})^2` with `K = 19781/125` (`UpperMoment`). For a
budget `B` with `4*2^L ≤ B < 8*2^L`, the dyadic family of `BlindUpper` runs
level `L` and leaves up to half the budget unused. Here the estimator runs
level `L+1` with probability `p = B/(4*2^L) - 1` and level `L` otherwise, so its
expected work is at most `(1-p)*4*2^L + p*8*2^L = B`. Since
`N*ω(N^{-1/2})^2 ≤ B*ω(B^{-1/2})^2` for `N ≤ B`, its mean-square error is at
most `K*ω(B^{-1/2})^2*4*(1+p)*(1-p/2) ≤ (9/2)*K*ω(B^{-1/2})^2`, and
`(9/2)*K = 178029/250 ≤ 27^2`. -/
noncomputable section
namespace ThresholdHC.UpperMixture
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.BlindUpper
open scoped ENNReal

/-- `ω(c*h) ≤ c*ω(h)` for `c ≥ 1`. -/
theorem modulus_mul_le (μ : Measure Gap) [IsProbabilityMeasure μ] {c h : ℝ} (hc : 1 ≤ c)
    (hh : 0 ≤ h) : modulus μ (c * h) ≤ c * modulus μ h := by
  have hc0 : 0 < c := by linarith
  have ht := modulus_scaling μ (1 / c) (c * h) (by positivity)
    (by rw [div_le_one hc0]; exact hc) (by positivity)
  have he : (1 / c) * (c * h) = h := by field_simp
  rw [he] at ht
  calc
    modulus μ (c * h) = c * ((1 / c) * modulus μ (c * h)) := by field_simp
    _ ≤ c * modulus μ h := mul_le_mul_of_nonneg_left ht hc0.le

/-- A smaller dyadic scale costs at most its share of the budget scale:
`N*ω(N^{-1/2})^2 ≤ B*ω(B^{-1/2})^2` for `0 < N ≤ B`. -/
theorem modulus_sq_scale (μ : Measure Gap) [IsProbabilityMeasure μ] {N B : ℝ} (hN : 0 < N)
    (hNB : N ≤ B) :
    N * (modulus μ (1 / Real.sqrt N)) ^ 2 ≤ B * (modulus μ (1 / Real.sqrt B)) ^ 2 := by
  have hB : 0 < B := hN.trans_le hNB
  have hc : 1 ≤ Real.sqrt (B / N) := by
    rw [Real.one_le_sqrt]
    exact (one_le_div hN).2 hNB
  have h1 : 1 / Real.sqrt N = Real.sqrt (B / N) * (1 / Real.sqrt B) := by
    rw [Real.sqrt_div' B hN.le]
    have hsN := Real.sqrt_pos.2 hN
    have hsB := Real.sqrt_pos.2 hB
    field_simp
  have hm := modulus_mul_le μ hc (h := 1 / Real.sqrt B) (by positivity)
  rw [← h1] at hm
  have h0 : 0 ≤ modulus μ (1 / Real.sqrt N) := modulus_nonneg μ (by positivity)
  have hsq : (modulus μ (1 / Real.sqrt N)) ^ 2 ≤ (B / N) * (modulus μ (1 / Real.sqrt B)) ^ 2 := by
    calc
      _ ≤ (Real.sqrt (B / N) * modulus μ (1 / Real.sqrt B)) ^ 2 := pow_le_pow_left₀ h0 hm 2
      _ = (Real.sqrt (B / N)) ^ 2 * (modulus μ (1 / Real.sqrt B)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  calc
    N * (modulus μ (1 / Real.sqrt N)) ^ 2 ≤ N * ((B / N) * (modulus μ (1 / Real.sqrt B)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hN.le
    _ = _ := by field_simp

/-- The squared risk of the calibrated batch at level `L`. -/
theorem batch_squaredRisk_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    squaredRisk (experimentLaw μ (batchEstimator L) q) (populationOutput (batchEstimator L))
        (signMean μ q.val) ≤
      ENNReal.ofReal ((19781/125) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) := by
  rw [batch_squaredRisk_eq]
  exact UpperMoment.cutoffBatch_mse L μ q

theorem batchEstimator_randomLaw (L : ℕ) : (batchEstimator L).randomLaw = batchSeedLaw := rfl

theorem batch_randomLaw_succ (L : ℕ) :
    (batchEstimator (L + 1)).randomLaw = (batchEstimator L).randomLaw :=
  (batchEstimator_randomLaw (L + 1)).trans (batchEstimator_randomLaw L).symm

/-- The weight of the higher level for a budget `B`. -/
def levelWeight (B : ℝ) : ℝ := B / (4 * (2 : ℝ) ^ (budgetLevel B)) - 1

theorem levelWeight_bounds (B : ℝ) (hB : 4 ≤ B) : 0 ≤ levelWeight B ∧ levelWeight B ≤ 1 := by
  obtain ⟨h1, h2⟩ := budgetLevel_bounds B hB
  have hN : 0 < 4 * (2 : ℝ) ^ (budgetLevel B) := by positivity
  unfold levelWeight
  constructor
  · rw [sub_nonneg, le_div_iff₀ hN]
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hN]
    linarith

theorem levelWeight_budget (B : ℝ) :
    4 * (2 : ℝ) ^ (budgetLevel B) * (1 + levelWeight B) = B := by
  have hN : 0 < 4 * (2 : ℝ) ^ (budgetLevel B) := by positivity
  unfold levelWeight
  field_simp
  ring

/-- The budget-indexed family: the mixture of the two dyadic levels around `B/4`,
and an estimator that does no work for budgets below four. -/
def budgetMixture (B : ℝ) : AdaptiveEstimator (Bool × BatchSeed) :=
  if 4 ≤ B then
    mixEstimator (levelWeight B) (batchEstimator (budgetLevel B)) (batchEstimator (budgetLevel B + 1))
  else mixEstimator 0 idleBatchEstimator idleBatchEstimator

theorem budgetMixture_uniformBudget (B : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    UniformBudget μ (budgetMixture B) B := by
  intro q
  by_cases hlarge : 4 ≤ B
  · rw [budgetMixture, ite_eq_left hlarge, mix_expectedWork (levelWeight B)
      (batchEstimator (budgetLevel B)) (batchEstimator (budgetLevel B + 1))
      (batch_randomLaw_succ _)]
    obtain ⟨hp0, hp1⟩ := levelWeight_bounds B hlarge
    rw [clip_eq hp0 hp1]
    set L := budgetLevel B
    set p := levelWeight B
    have h1 := batch_uniformBudget (L + 1) μ q
    have h0 := batch_uniformBudget L μ q
    have hN : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
    calc
      _ ≤ ENNReal.ofReal p * ENNReal.ofReal (4 * (2 : ℝ) ^ (L + 1)) +
          ENNReal.ofReal (1 - p) * ENNReal.ofReal (4 * (2 : ℝ) ^ L) := by gcongr
      _ = ENNReal.ofReal (p * (4 * (2 : ℝ) ^ (L + 1)) + (1 - p) * (4 * (2 : ℝ) ^ L)) := by
        rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) (by positivity))]
      _ = ENNReal.ofReal B := by
        congr 1
        rw [← levelWeight_budget B, pow_succ]
        ring
  · rw [budgetMixture, ite_eq_right hlarge, mix_expectedWork 0 idleBatchEstimator
      idleBatchEstimator rfl, idleBatch_expectedWork_zero]
    simp

theorem idleMixture_maximalRMSRisk (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (mixEstimator 0 idleBatchEstimator idleBatchEstimator) ≤ 1 := by
  refine le_trans (le_of_eq ?_) (idleBatch_maximalRMSRisk μ)
  unfold maximalRMSRisk rootMeanRisk
  congr 1
  funext q
  rw [mix_squaredRisk 0 idleBatchEstimator idleBatchEstimator rfl]
  simp [clip]

theorem budgetMixture_maximalRMSRisk (B : ℝ) (hB : 1 ≤ B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (budgetMixture B) ≤ ENNReal.ofReal (27 * modulus μ (1 / Real.sqrt B)) := by
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
    have hmix : p * ((19781/125) * b ^ 2) + (1 - p) * ((19781/125) * a ^ 2) ≤ (27 * w) ^ 2 := by
      have ha' : a ^ 2 ≤ 4 * (1 + p) * w ^ 2 := by
        rw [← hbud] at ha
        have h4 : 0 < 4 * (1 + p) := by linarith
        nlinarith
      have hb' : b ^ 2 ≤ 2 * (1 + p) * w ^ 2 := by
        rw [← hbud] at hb
        nlinarith
      have hq : (1 + p) * (4 - 2 * p) ≤ 9 / 2 := by nlinarith [sq_nonneg (p - 1 / 2)]
      have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
      nlinarith [mul_le_mul_of_nonneg_left hb' hp0, mul_le_mul_of_nonneg_left ha' (by linarith : 0 ≤ 1 - p),
        mul_le_mul_of_nonneg_right hq hw2]
    apply iSup_le
    intro q
    unfold rootMeanRisk
    have hsq : squaredRisk (experimentLaw μ (mixEstimator p (batchEstimator L) (batchEstimator (L + 1))) q)
        (populationOutput (mixEstimator p (batchEstimator L) (batchEstimator (L + 1))))
        (signMean μ q.val) ≤ ENNReal.ofReal ((27 * w) ^ 2) := by
      rw [mix_squaredRisk p (batchEstimator L) (batchEstimator (L + 1)) (batch_randomLaw_succ L),
        clip_eq hp0 hp1]
      calc
        _ ≤ ENNReal.ofReal p * ENNReal.ofReal ((19781/125) * b ^ 2) +
            ENNReal.ofReal (1 - p) * ENNReal.ofReal ((19781/125) * a ^ 2) := by
          gcongr
          · exact batch_squaredRisk_le (L + 1) μ q
          · exact batch_squaredRisk_le L μ q
        _ = ENNReal.ofReal (p * ((19781/125) * b ^ 2) + (1 - p) * ((19781/125) * a ^ 2)) := by
          rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul (by linarith),
            ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) (by positivity))]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hmix
    have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [ofReal_square_rpow_half (27 * w) (by positivity)] at hr
  · rw [budgetMixture, ite_eq_right hlarge, smallBudget_modulus μ B hB (lt_of_not_ge hlarge)]
    exact (idleMixture_maximalRMSRisk μ).trans (by norm_num)

theorem blind_upper_27 : BlindUpper27Statement := by
  refine ⟨Bool × BatchSeed, inferInstance, budgetMixture, ?_⟩
  intro B hB μ _
  exact ⟨budgetMixture_uniformBudget B μ, budgetMixture_maximalRMSRisk B hB μ⟩

theorem minimax_upper_27 : MinimaxUpper27Statement := by
  intro μ _ B hB
  apply le_trans ?_ (budgetMixture_maximalRMSRisk B hB μ)
  apply sInf_le
  exact ⟨Bool × BatchSeed, inferInstance, budgetMixture B, budgetMixture_uniformBudget B μ, rfl⟩

end ThresholdHC.UpperMixture
