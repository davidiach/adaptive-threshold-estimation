import ThresholdHC.UnbiasedConverse.LocalConverse
import ThresholdHC.UnbiasedConverse.InverseMoment

noncomputable section
open MeasureTheory
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC.Tier6

/-- The full observable-algorithm converse, with the paper's coefficient 1/16. -/
theorem unbiased_converse : UnbiasedConverseStatement := by
  intro R _ μ _ A V W hV hW hu hv hw
  have hVW : 0 ≤ V*W := mul_nonneg hV hW
  have hs := Real.sq_sqrt hVW
  obtain ⟨hi, hI⟩ := inverse_integrable_of_modulus_bound μ
    (show 0 ≤ 4*Real.sqrt (V*W) by positivity) (by
      intro h hh
      have hb := modulus_square_bound μ A hV hW hu hv hw hh
      have hp : 0 ≤ 4*Real.sqrt (V*W)*h := by positivity
      nlinarith)
  refine ⟨hi, ?_⟩
  have hI0 : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂μ :=
    integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hsq := mul_self_le_mul_self hI0 hI
  nlinarith

theorem no_finite_variance_work_of_inverse_not_integrable
    {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (hI : ¬ Integrable (fun d : Gap => (d:ℝ)⁻¹) μ)
    (hu : UniformlyUnbiased μ A) :
    ¬ ∃ V W : ℝ, 0 ≤ V ∧ 0 ≤ W ∧ UniformVarianceBound μ A V ∧ UniformBudget μ A W := by
  rintro ⟨V,W,hV,hW,hv,hw⟩
  exact hI (unbiased_converse R μ A V W hV hW hu hv hw).1

end ThresholdHC.UnbiasedConverse
