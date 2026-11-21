import ThresholdHC.MarginClasses.Basic
import ThresholdHC.Observable713.Full
import ThresholdHC.SmoothDensity.Envelope

/-! The unbiased dichotomy of Corollary `cor:power`. For `α > 1` the 713
observable estimator, chosen before `α` and `C`, works on the whole class with
the inverse-moment bound `α C^{1/α}/(α-1)`. For `α ≤ 1` the linear law at the
reference scale lies in the class and its inverse gap is not integrable, so
the unbiased converse excludes every estimator. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.MarginClasses
open ThresholdHC.Tier6 ThresholdHC.UnbiasedConverse ThresholdHC.Observable713
open ThresholdHC.RareAboveTwo ThresholdHC.SmoothDensity

/-- The common unbiased estimator for every `α > 1`. -/
theorem common_unbiased_estimator : CommonUnbiasedStatement := by
  obtain ⟨A,hA⟩ := observable_713
  refine ⟨A,?_⟩
  intro α C hα hC ν _ hν
  obtain ⟨hi,hI⟩ := power_inverse hα hC ν hν
  obtain ⟨hu,hv,hw,_⟩ := hA ν hi
  exact ⟨hu,fun q => (hv q).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hI (by norm_num))),
    fun q => (hw q).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hI (by norm_num)))⟩

/-- The linear law has a non-integrable inverse gap: its modulus is
`(h/a)(1 + log(a/h))`, which no linear bound `h I` dominates. -/
theorem linearLaw_not_integrable {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/2) :
    ¬ Integrable (fun d : Gap => (d:ℝ)⁻¹) (powerGapLaw 1 a (by norm_num) ha ha') := by
  intro hi
  have hI : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha') :=
    integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hx : 0 < a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1 := by
    have := mul_nonneg ha.le hI
    linarith
  have he := Real.exp_pos (-(a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1))
  have he1 : Real.exp (-(a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hh : 0 < a * Real.exp (-(a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1)) :=
    mul_pos ha he
  have hha : a * Real.exp (-(a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1)) < a := by
    nlinarith
  have hlm := linear_modulus a _ ha ha' hh hha
  have hub := modulus_le_inverse _ hi hh.le
  rw [hlm] at hub
  have h1 : a * Real.exp (-(a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1)) / a =
      Real.exp (-(a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1)) := by
    field_simp
  have h2 : a / (a * Real.exp (-(a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1))) =
      Real.exp (a * (∫ d : Gap, (d:ℝ)⁻¹ ∂(powerGapLaw 1 a (by norm_num) ha ha')) + 1) := by
    rw [Real.exp_neg]
    field_simp
  rw [h1,h2,Real.log_exp] at hub
  nlinarith

/-- The unbiased dichotomy on the whole class. -/
theorem unbiased_dichotomy : PowerUnbiasedStatement := by
  intro α C hα hC
  constructor
  · rintro ⟨R,mR,A,V,W,hV,hW,hA⟩
    by_contra h1
    have hα1 : α ≤ 1 := le_of_not_gt h1
    have hC0 := class_const_pos hC
    obtain ⟨hu,hv,hw⟩ := hA (powerGapLaw 1 (C^(-(1/α))) (by norm_num) (ref_pos hC0) (ref_le_half hα hC))
      (linearLaw_mem hα hα1 hC)
    exact linearLaw_not_integrable (ref_pos hC0) (ref_le_half hα hC)
      (unbiased_converse R _ A V W hV hW hu hv hw).1
  · intro h1
    obtain ⟨A,hA⟩ := common_unbiased_estimator
    have hJ : 0 ≤ α * C^(1/α) / (α - 1) :=
      div_nonneg (mul_nonneg hα.le (Real.rpow_nonneg (class_const_pos hC).le _)) (by linarith)
    exact ⟨ℕ,inferInstance,A,23 * (α * C^(1/α) / (α - 1)),31 * (α * C^(1/α) / (α - 1)),
      by positivity,by positivity,fun ν _ hν => hA α C h1 hC ν hν⟩

end ThresholdHC.MarginClasses
