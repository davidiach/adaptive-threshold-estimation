import ThresholdHC.Uniform713.Conditional
import ThresholdHC.Uniform713.Integration

/-!
The complete theorem: the conditional classifier analysis is discharged from
the observation model, then integrated over an arbitrary magnitude/sign law.
-/

noncomputable section

namespace ThresholdHC.Uniform713

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

theorem full_bound_713 : FullBound713Statement := by
  intro Θ Ω _ _ ν _ κ _ X d s model
  haveI : IsProbabilityMeasure (mixtureLaw ν κ) := by
    unfold mixtureLaw
    infer_instance
  have hm (k : ℕ) : Measurable (dyadicMean X k) :=
    measurable_prefixMean model.measurable_observations _
  have hz (l : ℕ) : Measurable (decisions X l) :=
    measurable_decision (dyadicMean X) hm l
  have hw (l : ℕ) : Measurable (levelWork X l) :=
    measurable_work (dyadicMean X) hm l
  have hY : Measurable (@uniformEstimator Θ Ω X) :=
    (measurable_estimator hz).comp measurable_snd
  have hW : Measurable (@uniformWork Θ Ω X) :=
    (measurable_sampled hw).comp measurable_snd
  have hW0 (x : Θ × (ℕ × Ω)) : 0 ≤ uniformWork X x := (work_pos _ _).le
  have hc : ∀ᵐ θ ∂ν,
      MemLp (estimator (decisions X)) 2 (samplingMeasure (κ θ)) ∧
      Integrable (sampled (levelWork X)) (samplingMeasure (κ θ)) ∧
      (∫ a, (estimator (decisions X) a) ^ 2 ∂samplingMeasure (κ θ)) < 23 / d θ ∧
      (∫ a, sampled (levelWork X) a ∂samplingMeasure (κ θ)) < 31 / d θ ∧
      (∫ a, estimator (decisions X) a ∂samplingMeasure (κ θ)) = signValue (s θ) := by
    filter_upwards [model.magnitude_range, model.bounded, model.mean, model.independent]
      with θ hd hb hp hi
    exact conditional_bounds (κ θ) X (d θ) (s θ) hd.1 hd.2
      (hasMeanTails_of_independent_bounded model.measurable_observations hb hp hi)
  have hY2i : ∀ᵐ θ ∂ν, Integrable
      (fun a => (uniformEstimator X (θ,a)) ^ 2) (samplingKernel κ θ) := by
    filter_upwards [hc] with θ hθ
    rw [samplingKernel_apply]
    exact hθ.1.integrable_sq
  have hY2b : ∀ᵐ θ ∂ν,
      (∫ a, (uniformEstimator X (θ,a)) ^ 2 ∂samplingKernel κ θ) < 23 / d θ := by
    filter_upwards [hc] with θ hθ
    rw [samplingKernel_apply]
    exact hθ.2.2.1
  have hWi : ∀ᵐ θ ∂ν, Integrable
      (fun a => uniformWork X (θ,a)) (samplingKernel κ θ) := by
    filter_upwards [hc] with θ hθ
    rw [samplingKernel_apply]
    exact hθ.2.1
  have hWb : ∀ᵐ θ ∂ν,
      (∫ a, uniformWork X (θ,a) ∂samplingKernel κ θ) ≤ 31 / d θ := by
    filter_upwards [hc] with θ hθ
    rw [samplingKernel_apply]
    exact hθ.2.2.2.1.le
  have hy2 := integrate_conditional_inverse_gap_strict
    (hY.pow_const 2) (fun x => sq_nonneg _) hY2i model.inverse_integrable hY2b
  have hw1 := integrate_conditional_inverse_gap hW hW0 hWi model.inverse_integrable hWb
  have hYL2 : MemLp (@uniformEstimator Θ Ω X) 2 (mixtureLaw ν κ) :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).2 hy2.1
  have hYint : Integrable (@uniformEstimator Θ Ω X) (mixtureLaw ν κ) :=
    hYL2.integrable (by norm_num)
  refine ⟨hYL2, hw1.1, ?_, ?_⟩
  · rw [mixtureLaw, Measure.integral_compProd hYint]
    apply integral_congr_ae
    filter_upwards [hc] with θ hθ
    rw [samplingKernel_apply]
    exact hθ.2.2.2.2
  · have hI : 0 < ∫ θ, (d θ)⁻¹ ∂ν := by
      have hnonneg : 0 ≤ ∫ x, (uniformEstimator X x)^2 ∂mixtureLaw ν κ :=
        integral_nonneg (fun x => sq_nonneg _)
      dsimp only [mixtureLaw] at hnonneg
      linarith [hy2.2]
    have hvar : ProbabilityTheory.variance (@uniformEstimator Θ Ω X) (mixtureLaw ν κ) ≤
        ∫ x, (uniformEstimator X x)^2 ∂mixtureLaw ν κ :=
      variance_le_expectation_sq hY.aestronglyMeasurable
    calc
      _ ≤ (∫ x, (uniformEstimator X x)^2 ∂mixtureLaw ν κ) *
          (∫ x, uniformWork X x ∂mixtureLaw ν κ) :=
        mul_le_mul_of_nonneg_right hvar (integral_nonneg hW0)
      _ ≤ (∫ x, (uniformEstimator X x)^2 ∂mixtureLaw ν κ) *
          (31 * ∫ θ, (d θ)⁻¹ ∂ν) :=
        mul_le_mul_of_nonneg_left hw1.2 (integral_nonneg (fun x => sq_nonneg _))
      _ < (23 * ∫ θ, (d θ)⁻¹ ∂ν) * (31 * ∫ θ, (d θ)⁻¹ ∂ν) :=
        mul_lt_mul_of_pos_right hy2.2 (by positivity)
      _ = _ := by ring

end ThresholdHC.Uniform713

#print axioms ThresholdHC.Uniform713.full_bound_713
