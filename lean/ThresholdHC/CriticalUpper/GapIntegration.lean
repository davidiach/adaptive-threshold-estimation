import ThresholdHC.CriticalEntropy.CriticalLaw
import ThresholdHC.CriticalEntropy.PopulationModel

/-! The squared-gap uniform law and the integrated majority-vote error. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy
open scoped ENNReal

theorem criticalGap_ae_support : ∀ᵐ d ∂criticalGapLaw, d ∈ Ioc (0 : ℝ) (1/4) := by
  exact criticalGapLaw_supported

theorem uniformUnitMeasure_Iic (x : ℝ) :
    uniformUnitMeasure (Iic x) = ENNReal.ofReal (min 1 x) := by
  rw [uniformUnitMeasure,Measure.restrict_apply measurableSet_Iic]
  have he : Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 (min 1 x) := by
    ext u
    simp only [mem_inter_iff,mem_Iic,mem_Icc,le_min_iff]
    tauto
  rw [he]
  simp

/-- Squared normalized gap is exactly uniform for the fixed quadratic law. -/
theorem criticalGap_square_map : criticalGapLaw.map (fun d : ℝ => 16*d^2) = uniformUnitMeasure := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,uniformUnitMeasure_Iic]
  by_cases hx : 0 ≤ x
  · by_cases hx1 : x ≤ 1
    · have hy : Real.sqrt x/4 ≤ 1/4 := by
        nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg x]
      have he : (fun d : ℝ => 16*d^2) ⁻¹' Iic x =ᵐ[criticalGapLaw] Ioc 0 (Real.sqrt x/4) := by
        filter_upwards [criticalGap_ae_support] with d hd
        apply propext
        simp only [mem_preimage,mem_Iic,mem_Ioc,hd.1,true_and]
        constructor <;> intro h <;> nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg x,hd.1]
      rw [measure_congr he,criticalGapLaw_Ioc 0 (Real.sqrt x/4) (by norm_num) (by positivity) hy,
        min_eq_right hx1]
      congr 1
      nlinarith [Real.sq_sqrt hx]
    · have he : (fun d : ℝ => 16*d^2) ⁻¹' Iic x =ᵐ[criticalGapLaw] univ := by
        filter_upwards [criticalGap_ae_support] with d hd
        apply propext
        simp only [mem_preimage,mem_Iic,mem_univ,iff_true]
        nlinarith [hd.1,hd.2]
      rw [measure_congr he,measure_univ,min_eq_left (le_of_not_ge hx1)]
      simp
  · have he : (fun d : ℝ => 16*d^2) ⁻¹' Iic x = ∅ := by
      ext d
      simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      nlinarith [sq_nonneg d]
    rw [he,measure_empty,ENNReal.ofReal_of_nonpos (le_trans (min_le_right _ _) (le_of_not_ge hx))]

theorem criticalGap_square_preserving :
    MeasurePreserving (fun d : ℝ => 16*d^2) criticalGapLaw uniformUnitMeasure :=
  ⟨by fun_prop,criticalGap_square_map⟩

theorem uniformUnit_laplace (t : ℝ) (ht : 0 < t) :
    (∫ u, Real.exp (-t*u) ∂uniformUnitMeasure) = (1-Real.exp (-t))/t := by
  unfold uniformUnitMeasure
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr ht.ne'),integral_exp]
  simp only [mul_one,mul_zero,Real.exp_zero,smul_eq_mul]
  field_simp
  ring

theorem criticalGap_laplace (t : ℝ) (ht : 0 < t) :
    (∫ d, Real.exp (-t*(16*d^2)) ∂criticalGapLaw) = (1-Real.exp (-t))/t := by
  rw [← uniformUnit_laplace t ht,← criticalGap_square_map,
    integral_map (by fun_prop) (by fun_prop)]

theorem criticalGaussian_integrable (N : ℝ) (hN : 0 < N) :
    Integrable (fun d : ℝ => Real.exp (-2*N*d^2)) criticalGapLaw := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg d])

/-- Exact quadratic-law control of the capped-majority error integral. -/
theorem criticalGaussian_integral_le (N : ℝ) (hN : 0 < N) :
    (∫ d, Real.exp (-2*N*d^2) ∂criticalGapLaw) ≤ 8/N := by
  calc
    _ = ∫ d, Real.exp (-(N/8)*(16*d^2)) ∂criticalGapLaw := by
      apply integral_congr_ae
      exact ae_of_all _ (fun d => congrArg Real.exp (by ring))
    _ = (1-Real.exp (-(N/8)))/(N/8) := criticalGap_laplace _ (by positivity)
    _ ≤ 1/(N/8) := div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-(N/8))]) (by positivity)
    _ = _ := by field_simp

end ThresholdHC.CriticalUpper
