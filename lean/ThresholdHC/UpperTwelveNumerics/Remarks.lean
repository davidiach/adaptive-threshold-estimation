import ThresholdHC.UpperTwelveNumerics.Specification
import ThresholdHC.UpperCallCost.Batch
import ThresholdHC.UpperCost.Full
import ThresholdHC.BlindUpper.Full

/-! The remarks after the proof of the upper constant 12.

The calibrated batch at level `L` has mean-square error at most
`(174/5)*ω(2^{-L/2})^2` (`UpperCallCost.cutoffBatch_mse`).

* The two-level mixture `UpperMixture.budgetMixture` turns a batch factor `K`
  into the RMS constant `sqrt((9/2)*K)` (`UpperCost.budgetMixture_risk_of_batch`),
  here `sqrt(783/5)`, between `12.51` and `12.52`.
* The dyadic family `BlindUpper.budgetEstimator` runs the batch at the level `L`
  with `4*2^L ≤ B < 8*2^L`. Since `2^L*ω(2^{-L/2})^2 ≤ B*ω(B^{-1/2})^2`, it pays
  the factor `B/2^L < 8`, whose supremum `8` is approached at `B` just below
  `8` (where `L = 0`). Its RMS constant is at most `sqrt(8*174/5)`.
* At the calibration scale `B/4`, the squared bias of the level-`L` call is at
  most `ω(2^{-L/2})^2 ≤ λ*ω((B/4)^{-1/2})^2` with `λ = B/(4*2^L) ∈ [1, 2)`, and
  `ω((B/4)^{-1/2})^2 ≤ 4*ω(B^{-1/2})^2`. -/
noncomputable section
namespace ThresholdHC.UpperTwelveNumerics
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6
open scoped ENNReal

/-- The squared risk of the calibrated batch at level `L`, with the factor `174/5`. -/
theorem batch_squaredRisk_call (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    squaredRisk (experimentLaw μ (BlindUpper.batchEstimator L) q)
        (populationOutput (BlindUpper.batchEstimator L)) (signMean μ q.val) ≤
      ENNReal.ofReal ((174/5) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) := by
  rw [BlindUpper.batch_squaredRisk_eq]
  exact UpperCallCost.cutoffBatch_mse L μ q

/-! ### The two-level mixture -/

theorem mixture_constant_bounds :
    (1251/100 : ℝ) < Real.sqrt ((9/2) * (174/5)) ∧ Real.sqrt ((9/2) * (174/5)) < 1252/100 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

theorem budgetMixture_risk_call (B : ℝ) (hB : 1 ≤ B) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (Real.sqrt ((9/2) * (174/5)) * modulus μ (1 / Real.sqrt B)) :=
  UpperCost.budgetMixture_risk_of_batch (K := 174/5) (by norm_num)
    (Real.one_le_sqrt.2 (by norm_num)) (Real.sq_sqrt (by norm_num)).ge
    (fun L μ _ q => batch_squaredRisk_call L μ q) B hB μ

/-! ### The dyadic batch -/

theorem dyadic_ratio_lt (B : ℝ) (hB : 4 ≤ B) : B / (2 : ℝ) ^ BlindUpper.budgetLevel B < 8 := by
  have h := (BlindUpper.budgetLevel_bounds B hB).2
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- Below `8` the level is `0`. -/
theorem budgetLevel_eq_zero (B : ℝ) (hB : 4 ≤ B) (h8 : B < 8) : BlindUpper.budgetLevel B = 0 := by
  have h := (BlindUpper.budgetLevel_bounds B hB).1
  by_contra hL
  have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ BlindUpper.budgetLevel B :=
    pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.2 hL)
  norm_num at h2
  linarith

theorem dyadic_ratio_sup (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 4 ≤ B ∧ 8 - ε < B / (2 : ℝ) ^ BlindUpper.budgetLevel B := by
  refine ⟨max 4 (8 - ε / 2), le_max_left _ _, ?_⟩
  have h8 : max 4 (8 - ε / 2) < 8 := max_lt (by norm_num) (by linarith)
  rw [budgetLevel_eq_zero _ (le_max_left _ _) h8, pow_zero, div_one]
  exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

theorem budgetEstimator_risk_call (B : ℝ) (hB : 1 ≤ B) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ (BlindUpper.budgetEstimator B) ≤
      ENNReal.ofReal (Real.sqrt (8 * (174/5)) * modulus μ (1 / Real.sqrt B)) := by
  have hc1 : 1 ≤ Real.sqrt (8 * (174/5)) := Real.one_le_sqrt.2 (by norm_num)
  by_cases hlarge : 4 ≤ B
  · rw [BlindUpper.budgetEstimator, ite_eq_left hlarge]
    obtain ⟨h1, h2⟩ := BlindUpper.budgetLevel_bounds B hlarge
    set L := BlindUpper.budgetLevel B with hL
    set N : ℝ := (2 : ℝ) ^ L with hNdef
    have hN : 0 < N := by positivity
    set w := modulus μ (1 / Real.sqrt B) with hwdef
    set a := modulus μ (1 / Real.sqrt N) with hadef
    have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
    have ha : N * a ^ 2 ≤ B * w ^ 2 := UpperMixture.modulus_sq_scale μ hN (by linarith)
    have ha' : a ^ 2 ≤ 8 * w ^ 2 := by
      have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
      have : N * a ^ 2 ≤ N * (8 * w ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this hN
    apply iSup_le
    intro q
    unfold rootMeanRisk
    have hsq : squaredRisk (experimentLaw μ (BlindUpper.batchEstimator L) q)
        (populationOutput (BlindUpper.batchEstimator L)) (signMean μ q.val) ≤
        ENNReal.ofReal ((Real.sqrt (8 * (174/5)) * w) ^ 2) := by
      refine (batch_squaredRisk_call L μ q).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      change (174/5) * a ^ 2 ≤ 8 * (174/5) * w ^ 2
      nlinarith
    have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1/2)
    rwa [ofReal_square_rpow_half _ (by positivity)] at hr
  · rw [BlindUpper.budgetEstimator, ite_eq_right hlarge,
      BlindUpper.smallBudget_modulus μ B hB (lt_of_not_ge hlarge)]
    exact (BlindUpper.idleBatch_maximalRMSRisk μ).trans ((le_of_eq ENNReal.ofReal_one.symm).trans
      (ENNReal.ofReal_le_ofReal (by rw [mul_one]; exact hc1)))

/-! ### The bias at the calibration scale `B/4` -/

theorem scaleFour_bias (B : ℝ) (hB : 4 ≤ B) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) :
    1 ≤ B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) ∧
    B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) < 2 ∧
    ((∫ z, BlindUpper.cutoffValue (BlindUpper.budgetLevel B) z ∂BlindUpper.callMeasure μ q) -
        signMean μ q.val) ^ 2 ≤
      B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) * modulus μ (1 / Real.sqrt (B / 4)) ^ 2 ∧
    modulus μ (1 / Real.sqrt (B / 4)) ^ 2 ≤ 4 * modulus μ (1 / Real.sqrt B) ^ 2 := by
  obtain ⟨h1, h2⟩ := BlindUpper.budgetLevel_bounds B hB
  set L := BlindUpper.budgetLevel B with hL
  set N : ℝ := (2 : ℝ) ^ L with hNdef
  have hN : 0 < N := by positivity
  have h4N : 0 < 4 * N := by positivity
  have hB0 : 0 < B := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h4N]
    linarith
  · rw [div_lt_iff₀ h4N]
    linarith
  · set b := (∫ z, BlindUpper.cutoffValue L z ∂BlindUpper.callMeasure μ q) - signMean μ q.val
      with hbdef
    set wL := modulus μ (1 / Real.sqrt N) with hwL
    set w4 := modulus μ (1 / Real.sqrt (B / 4)) with hw4
    have hwL0 : 0 ≤ wL := modulus_nonneg μ (by positivity)
    have hb : |b| ≤ wL :=
      (BlindUpper.cutoff_call_bias_le L μ q).trans (BlindUpper.callBiasScale_integral_le_modulus L μ)
    have hb2 : b ^ 2 ≤ wL ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hwL0).mpr hb
    have hs : N * wL ^ 2 ≤ (B / 4) * w4 ^ 2 :=
      UpperMixture.modulus_sq_scale μ hN (by linarith)
    have hwL2 : wL ^ 2 ≤ B / (4 * N) * w4 ^ 2 := by
      have he : B / (4 * N) * w4 ^ 2 = ((B / 4) * w4 ^ 2) / N := by
        field_simp
      rw [he, le_div_iff₀ hN]
      linarith
    exact hb2.trans hwL2
  · have hs := UpperMixture.modulus_sq_scale μ (N := B / 4) (B := B) (by positivity) (by linarith)
    set w4 := modulus μ (1 / Real.sqrt (B / 4)) with hw4
    set w := modulus μ (1 / Real.sqrt B) with hw
    have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
    nlinarith

end ThresholdHC.UpperTwelveNumerics
