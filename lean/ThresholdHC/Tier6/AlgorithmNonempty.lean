import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.Tier5.StoppingBase

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

/-- The estimator that immediately stops and returns zero. -/
def immediateEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ _ => none
  policy_measurable := by
    intro xs a
    exact measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

theorem immediate_expectedWork_zero (hreal : PopulationRealizationStatement)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    expectedWork μ immediateEstimator q = 0 := by
  have hr := hreal Unit μ immediateEstimator q
  letI : IsProbabilityMeasure (experimentLaw μ immediateEstimator q) := hr.1
  have hv : ∀ᵐ z ∂experimentLaw μ immediateEstimator q, ∀ n,
      (z.2 n).isSome =
        (populationPolicy immediateEstimator z.1 (processHistory z.2 n)).isSome := by
    apply ae_all_iff.mpr
    intro n
    exact realized_creation_valid_step (populationSeedLaw μ immediateEstimator)
      (experimentLaw μ immediateEstimator q) Prod.fst Prod.snd
      (populationPolicy immediateEstimator) populationGap (populationPrior q)
      measurable_fst (fun k b => measurableSet_eq_fun
        ((measurable_pi_apply k).comp measurable_snd) measurable_const)
      (measurable_populationPolicy immediateEstimator) hr.2 n
  have hz : ∀ᵐ z ∂experimentLaw μ immediateEstimator q, totalProcessWork z.2 = 0 := by
    filter_upwards [hv] with z hz
    have hzero (n : ℕ) : (z.2 n).isSome = false := by
      simpa only [populationPolicy, immediateEstimator, Option.isSome_none] using hz n
    simp [totalProcessWork, workOf, processPrefix, hzero]
  unfold expectedWork
  calc
    _ = ∫⁻ _z, (0 : ℝ≥0∞) ∂experimentLaw μ immediateEstimator q := lintegral_congr_ae hz
    _ = 0 := by simp

theorem budgetClassNonempty_of_realization (hreal : PopulationRealizationStatement) :
    BudgetClassNonemptyStatement := by
  intro μ _ B hB
  refine ⟨immediateEstimator, ?_⟩
  intro q
  rw [immediate_expectedWork_zero hreal]
  exact bot_le

theorem signMean_bounds (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ 1 := by
  have hi : Integrable q.val μ := by
    apply (integrable_const (1 : ℝ)).mono' q.property.1.aestronglyMeasurable
    filter_upwards [] with d
    rw [Real.norm_of_nonneg (q.property.2 d).1]
    exact (q.property.2 d).2
  refine ⟨integral_nonneg (fun d => (q.property.2 d).1), ?_⟩
  calc
    signMean μ q.val ≤ ∫ _ : Gap, (1 : ℝ) ∂μ :=
      integral_mono hi (integrable_const _) (fun d => (q.property.2 d).2)
    _ = 1 := by simp

/-- The nonempty budget class contains an estimator with finite worst-case risk. -/
theorem immediate_maximalRMSRisk_le_one (hreal : PopulationRealizationStatement)
    (μ : Measure Gap) [IsProbabilityMeasure μ] :
    maximalRMSRisk μ immediateEstimator ≤ 1 := by
  apply iSup_le
  intro q
  have hr := hreal Unit μ immediateEstimator q
  letI : IsProbabilityMeasure (experimentLaw μ immediateEstimator q) := hr.1
  have hmean := signMean_bounds μ q
  unfold rootMeanRisk
  apply ENNReal.rpow_le_one ?_ (by norm_num)
  have heq : squaredRisk (experimentLaw μ immediateEstimator q)
      (populationOutput immediateEstimator) (signMean μ q.val) =
      ENNReal.ofReal ((signMean μ q.val)^2) := by
    simp [squaredRisk, populationOutput, immediateEstimator]
  rw [heq]
  have hsq : (signMean μ q.val)^2 ≤ 1 := by nlinarith [hmean.1, hmean.2]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hsq

end ThresholdHC.Tier6
