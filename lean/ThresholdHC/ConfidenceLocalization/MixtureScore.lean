import ThresholdHC.ConfidenceLocalization.CappedMixture

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem half_mixture_mean {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q M : Measure I) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (hM : M = (1/2 : ℝ≥0) • P + (1/2 : ℝ≥0) • Q) (f : I → ℝ) :
    (∫ i, f i ∂M) = ((∫ i, f i ∂P)+(∫ i, f i ∂Q))/2 := by
  rw [hM,integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_nnreal_measure,integral_smul_nnreal_measure]
  norm_num only [NNReal.smul_def,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one,smul_eq_mul]
  ring

theorem half_mixture_variance {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q M : Measure I) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (hM : M = (1/2 : ℝ≥0) • P + (1/2 : ℝ≥0) • Q) (f : I → ℝ) :
    variance f P ≤ 2*variance f M := by
  let a := ∫ i, f i ∂M
  let g := fun i => f i-a
  have hp : variance f P ≤ ∫ i, (g i)^2 ∂P := by
    have h := variance_le_expectation_sq (μ := P) (measurable_of_countable g).aestronglyMeasurable
    rwa [variance_sub_const (measurable_of_countable f).aestronglyMeasurable] at h
  have hm : variance f M = ((∫ i, (g i)^2 ∂P)+(∫ i, (g i)^2 ∂Q))/2 := by
    rw [variance_eq_integral (measurable_of_countable f).aemeasurable]
    exact half_mixture_mean P Q M hM (fun i => (g i)^2)
  have hq : 0 ≤ ∫ i, (g i)^2 ∂Q := integral_nonneg (fun i => sq_nonneg _)
  linarith

/-- Recentring a score learned on half-regularized priors recovers the original
target with twice the bias bound and at most twice the variance. -/
theorem half_score_transfer {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q M : Measure I) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (hM : M = (1/2 : ℝ≥0) • P + (1/2 : ℝ≥0) • Q)
    (f : I → ℝ) (c θ ε V : ℝ) (hV : 0 ≤ V)
    (hb : |(∫ i, f i ∂M)-(θ+c)/2| ≤ ε)
    (hv : evariance f M ≤ ENNReal.ofReal V) :
    let Z := fun i => f i+((∫ j, f j ∂Q)-c)
    |(∫ i, Z i ∂P)-θ| ≤ 2*ε ∧ evariance Z P ≤ ENNReal.ofReal (2*V) := by
  dsimp only
  constructor
  · rw [integral_add Integrable.of_finite (integrable_const _),
      integral_const,probReal_univ,smul_eq_mul,one_mul]
    have he := half_mixture_mean P Q M hM f
    have h : (∫ i, f i ∂P)+((∫ i, f i ∂Q)-c)-θ =
        2*((∫ i, f i ∂M)-(θ+c)/2) := by linarith
    rw [h,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  · rw [← ofReal_variance (finite_function_memLp P _),
      variance_add_const (measurable_of_countable f).aestronglyMeasurable]
    apply ENNReal.ofReal_le_ofReal
    have h : variance f M ≤ V := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
      rwa [ENNReal.toReal_ofReal hV] at h
    exact (half_mixture_variance P Q M hM f).trans (mul_le_mul_of_nonneg_left h (by norm_num))

end ThresholdHC.ConfidenceLocalization
