import ThresholdHC.Envelope.Moments
import ThresholdHC.Observable713.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Envelope
open ThresholdHC.Tier6 ThresholdHC.UnbiasedConverse ThresholdHC.Observable713

/-- Both uniform bounds apply to the same estimator throughout the envelope. -/
def UnbiasedAt {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    (A : AdaptiveEstimator R) (V W : ℝ) : Prop :=
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], Within μ ν →
    UniformlyUnbiased ν A ∧ UniformVarianceBound ν A V ∧ UniformBudget ν A W

/-- The 713 estimator is chosen before even the reference envelope is given.
The individual bounds also control the product of the two separate suprema. -/
theorem blind_unbiased_upper :
    ∃ A : AdaptiveEstimator ℕ, ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    Integrable (fun d : Gap => (d:ℝ)⁻¹) μ →
      UnbiasedAt μ A (23*∫ d : Gap, (d:ℝ)⁻¹ ∂μ) (31*∫ d : Gap, (d:ℝ)⁻¹ ∂μ) := by
  obtain ⟨A,hA⟩ := observable_713
  refine ⟨A,?_⟩
  intro μ _ hμ ν _ h
  obtain ⟨hi,hI⟩ := inverse_moment_le μ ν h hμ
  obtain ⟨hu,hv,hw,_⟩ := hA ν hi
  refine ⟨hu,fun q => (hv q).trans (ENNReal.ofReal_le_ofReal ?_),
    fun q => (hw q).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact mul_le_mul_of_nonneg_left hI (by norm_num)
  · exact mul_le_mul_of_nonneg_left hI (by norm_num)

theorem unbiased_lower {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) (h : UnbiasedAt μ A V W) :
    Integrable (fun d : Gap => (d:ℝ)⁻¹) μ ∧ (∫ d : Gap, (d:ℝ)⁻¹ ∂μ)^2/16 ≤ V*W := by
  obtain ⟨hu,hv,hw⟩ := h μ (within_self μ)
  exact unbiased_converse R μ A V W hV hW hu hv hw

/-- Infimum of the variance-work products of finite uniform bounds. The
worst variance and worst work may occur at different laws or sign priors. -/
def varianceWork (μ : Measure Gap) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (V W : ℝ),
    0 ≤ V ∧ 0 ≤ W ∧ UnbiasedAt μ A V W ∧ t = ENNReal.ofReal (V*W)}

theorem unbiased_iff (μ : Measure Gap) [IsProbabilityMeasure μ] :
    (∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (V W : ℝ),
      0 ≤ V ∧ 0 ≤ W ∧ UnbiasedAt μ A V W) ↔ Integrable (fun d : Gap => (d:ℝ)⁻¹) μ := by
  constructor
  · rintro ⟨R,mR,A,V,W,hV,hW,h⟩
    exact (unbiased_lower μ A hV hW h).1
  · intro hi
    obtain ⟨A,hA⟩ := blind_unbiased_upper
    have hI : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂μ := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
    exact ⟨ℕ,inferInstance,A,_,_,mul_nonneg (by norm_num) hI,mul_nonneg (by norm_num) hI,hA μ hi⟩

theorem variance_work_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hi : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) :
    let I := ∫ d : Gap, (d:ℝ)⁻¹ ∂μ
    ENNReal.ofReal (I^2/16) ≤ varianceWork μ ∧ varianceWork μ ≤ ENNReal.ofReal (713*I^2) := by
  let I := ∫ d : Gap, (d:ℝ)⁻¹ ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  constructor
  · apply le_sInf
    rintro t ⟨R,mR,A,V,W,hV,hW,h,rfl⟩
    exact ENNReal.ofReal_le_ofReal (unbiased_lower μ A hV hW h).2
  · obtain ⟨A,hA⟩ := blind_unbiased_upper
    refine sInf_le ⟨ℕ,inferInstance,A,23*I,31*I,mul_nonneg (by norm_num) hI,mul_nonneg (by norm_num) hI,hA μ hi,?_⟩
    congr 1
    ring

end ThresholdHC.Envelope
