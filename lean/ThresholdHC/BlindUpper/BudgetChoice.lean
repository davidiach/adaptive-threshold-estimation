import ThresholdHC.BlindUpper.BatchMachine
import ThresholdHC.Tier6.AlgorithmNonempty
import ThresholdHC.Tier6.RiskReduction

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem modulus_mono (μ : Measure Gap) [IsProbabilityMeasure μ] {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : modulus μ x ≤ modulus μ y :=
  integral_mono (integrable_clippedGap μ hx) (integrable_clippedGap μ (hx.trans hxy))
    (fun d => min_le_min_left _ (div_le_div_of_nonneg_right hxy d.property.1.le))

theorem modulus_quadruple_le (μ : Measure Gap) [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 ≤ h) :
    modulus μ (4*h) ≤ 4*modulus μ h := by
  have ht := modulus_scaling μ (1/4) (4*h) (by norm_num) (by norm_num) (by positivity)
  have he : (1/4 : ℝ)*(4*h) = h := by ring
  rw [he] at ht
  linarith

theorem modulus_eq_one_of_half_le (μ : Measure Gap) [IsProbabilityMeasure μ] {h : ℝ}
    (hh : 1/2 ≤ h) : modulus μ h = 1 := by
  have he (d : Gap) : clippedGap h d = 1 :=
    min_eq_left ((one_le_div d.property.1).mpr (d.property.2.trans hh))
  simp [modulus,he]

theorem exists_budget_level (B : ℝ) (hB : 4 ≤ B) :
    ∃ L : ℕ, 4*(2 : ℝ)^L ≤ B ∧ B < 8*(2 : ℝ)^L := by
  obtain ⟨L,h₁,h₂⟩ := exists_nat_pow_near (x := B/4) (y := (2 : ℝ)) (by linarith) (by norm_num)
  rw [pow_succ] at h₂
  exact ⟨L,by linarith,by linarith⟩

def budgetLevel (B : ℝ) : ℕ :=
  if h : 4 ≤ B then Classical.choose (exists_budget_level B h) else 0

theorem budgetLevel_bounds (B : ℝ) (hB : 4 ≤ B) :
    4*(2 : ℝ)^(budgetLevel B) ≤ B ∧ B < 8*(2 : ℝ)^(budgetLevel B) := by
  simp only [budgetLevel,dite_eq_left hB]
  exact Classical.choose_spec (exists_budget_level B hB)

theorem budgetLevel_scale (B : ℝ) (hB : 4 ≤ B) :
    1/Real.sqrt ((2 : ℝ)^(budgetLevel B)) ≤ 4*(1/Real.sqrt B) := by
  have hN : 0 < (2 : ℝ)^(budgetLevel B) := by positivity
  have hB0 : 0 < B := by linarith
  have hsN := Real.sq_sqrt hN.le
  have hsB := Real.sq_sqrt hB0.le
  have hsN0 := Real.sqrt_pos.mpr hN
  have hsB0 := Real.sqrt_pos.mpr hB0
  have hroot : Real.sqrt B ≤ 4*Real.sqrt ((2 : ℝ)^(budgetLevel B)) := by
    nlinarith [(budgetLevel_bounds B hB).2]
  rw [show 4*(1/Real.sqrt B) = 4/Real.sqrt B by ring]
  exact (div_le_div_iff₀ hsN0 hsB0).mpr (by simpa using hroot)

theorem smallBudget_modulus (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ)
    (hB : 1 ≤ B) (hsmall : B < 4) : modulus μ (1/Real.sqrt B) = 1 := by
  have hB0 : 0 < B := by linarith
  have hs0 := Real.sqrt_pos.mpr hB0
  have hs := Real.sq_sqrt hB0.le
  apply modulus_eq_one_of_half_le
  apply (le_div_iff₀ hs0).mpr
  nlinarith

/-- Zero work for budgets too small for a calibrated batch, on the same seed
space used by every other budget. -/
def idleBatchEstimator : AdaptiveEstimator BatchSeed where
  randomLaw := batchSeedLaw
  probability := batchSeedLaw_probability
  policy := fun _ _ => none
  policy_measurable := by
    intro xs a
    exact measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

theorem idleBatch_expectedWork_zero (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    expectedWork μ idleBatchEstimator q = 0 := by
  rw [original_expectedWork_simulation]
  have hz (z : BatchSeed × (ℕ → ℕ → Bool)) :
      totalProcessWork (populationPath (idleBatchEstimator.policy z.1) z.2) = 0 := by
    have he : populationPath (idleBatchEstimator.policy z.1) z.2 = fun _ => none := by
      funext n
      simp [populationPath,populationSimulation,idleBatchEstimator]
    rw [he]
    simp [totalProcessWork,ThresholdHC.workOf,processPrefix]
  simp_rw [hz]
  simp

theorem idleBatch_maximalRMSRisk (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ idleBatchEstimator ≤ 1 := by
  apply iSup_le
  intro q
  unfold rootMeanRisk
  apply ENNReal.rpow_le_one ?_ (by norm_num)
  rw [original_squaredRisk_simulation]
  let : IsProbabilityMeasure (originalSimulationLaw μ idleBatchEstimator q) := by
    change IsProbabilityMeasure (batchSeedLaw.prod _)
    infer_instance
  change (∫⁻ z, ENNReal.ofReal ((0-signMean μ q.val)^2) ∂originalSimulationLaw μ idleBatchEstimator q) ≤ 1
  simp only [zero_sub,neg_sq,lintegral_const,measure_univ,mul_one]
  have hm := signMean_bounds μ q
  exact (ENNReal.ofReal_le_ofReal (by nlinarith [hm.1,hm.2] : (signMean μ q.val)^2 ≤ 1)).trans_eq
    ENNReal.ofReal_one

def budgetEstimator (B : ℝ) : AdaptiveEstimator BatchSeed :=
  if 4 ≤ B then batchEstimator (budgetLevel B) else idleBatchEstimator

end ThresholdHC.BlindUpper
