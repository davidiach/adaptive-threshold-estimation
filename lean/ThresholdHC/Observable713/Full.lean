import ThresholdHC.Observable713.Realization
import ThresholdHC.UnbiasedConverse.Full

/-! The 713 construction and unbiased existence characterization in the same observable model. -/

noncomputable section
namespace ThresholdHC.Observable713
open MeasureTheory ProbabilityTheory ThresholdHC.Tier6 ThresholdHC.UnbiasedConverse
open scoped ENNReal

theorem observable_713 : Observable713Statement := by
  refine ⟨observableEstimator, ?_⟩
  intro μ _ hI
  have hu : UniformlyUnbiased μ observableEstimator := fun q =>
    ⟨(output_memLp μ q hI).integrable (by norm_num),output_mean μ q hI⟩
  have hv : UniformVarianceBound μ observableEstimator (23*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) :=
    fun q => output_variance_le μ q hI
  have hw : UniformBudget μ observableEstimator (31*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) := by
    intro q
    rw [expectedWork_eq]
    exact call_work_le μ q hI
  refine ⟨hu,hv,hw,?_⟩
  calc
    _ ≤ ENNReal.ofReal (23*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) *
        ENNReal.ofReal (31*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) :=
      mul_le_mul' (iSup_le hv) (iSup_le hw)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num)
        (integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)))]
      congr 1
      ring

theorem observable_unbiased_iff : ObservableUnbiasedIffStatement := by
  intro μ _
  constructor
  · rintro ⟨R,mR,A,V,W,hV,hW,hu,hv,hw⟩
    let := mR
    exact (unbiased_converse R μ A V W hV hW hu hv hw).1
  · intro hI
    obtain ⟨A,hA⟩ := observable_713
    obtain ⟨hu,hv,hw,_⟩ := hA μ hI
    have hI0 : 0 ≤ ∫ d : Gap, (d : ℝ)⁻¹ ∂μ :=
      integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
    exact ⟨ℕ,inferInstance,A,23*∫ d : Gap, (d : ℝ)⁻¹ ∂μ,31*∫ d : Gap, (d : ℝ)⁻¹ ∂μ,
      mul_nonneg (by norm_num) hI0,mul_nonneg (by norm_num) hI0,hu,hv,hw⟩

end ThresholdHC.Observable713

#print axioms ThresholdHC.Observable713.observable_713
#print axioms ThresholdHC.Observable713.observable_unbiased_iff
