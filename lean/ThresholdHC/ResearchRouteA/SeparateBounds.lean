import ThresholdHC.ResearchRouteA.SeparateBoundsSpec
import ThresholdHC.Uniform713.Conditional
import ThresholdHC.Uniform713.Integration

/-! Proof prototype: acceptance requires the separately reviewed specification lock. -/

noncomputable section

namespace ThresholdHC.ResearchRouteA

open MeasureTheory ProbabilityTheory Filter ThresholdHC.Uniform713
open scoped ENNReal NNReal Topology

theorem separate_moment_bounds : SeparateMomentBoundsStatement := by
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
      (∫ a, (uniformEstimator X (θ,a)) ^ 2 ∂samplingKernel κ θ) ≤ 23 / d θ := by
    filter_upwards [hc] with θ hθ
    rw [samplingKernel_apply]
    exact hθ.2.2.1.le
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
  have hy2 := integrate_conditional_inverse_gap
    (hY.pow_const 2) (fun x => sq_nonneg _) hY2i model.inverse_integrable hY2b
  have hw1 := integrate_conditional_inverse_gap hW hW0 hWi model.inverse_integrable hWb
  exact ⟨(memLp_two_iff_integrable_sq hY.aestronglyMeasurable).2 hy2.1,
    hw1.1, hy2.2, hw1.2⟩

theorem uniform_family_bounds : UniformFamilyBoundsStatement := by
  intro Θ Ω _ _ κ _ X d s Γ _ ν I hprob hmodel hsame
  let v : Γ → ℝ := fun γ => variance (@uniformEstimator Θ Ω X) (mixtureLaw (ν γ) κ)
  let w : Γ → ℝ := fun γ => ∫ x, uniformWork X x ∂mixtureLaw (ν γ) κ
  have hv0 (γ : Γ) : 0 ≤ v γ := variance_nonneg _ _
  have hw0 (γ : Γ) : 0 ≤ w γ := integral_nonneg (fun x => (work_pos _ _).le)
  have hvb (γ : Γ) : v γ ≤ 23 * I := by
    haveI := hprob γ
    haveI : IsProbabilityMeasure (mixtureLaw (ν γ) κ) := by
      unfold mixtureLaw
      infer_instance
    have hb := separate_moment_bounds Θ Ω (ν γ) κ X d s (hmodel γ)
    calc
      _ ≤ ∫ x, (uniformEstimator X x)^2 ∂mixtureLaw (ν γ) κ :=
        variance_le_expectation_sq hb.1.aestronglyMeasurable
      _ ≤ 23 * I := by simpa only [hsame γ] using hb.2.2.1
  have hwb (γ : Γ) : w γ ≤ 31 * I := by
    haveI := hprob γ
    have hb := separate_moment_bounds Θ Ω (ν γ) κ X d s (hmodel γ)
    simpa only [hsame γ] using hb.2.2.2
  have hvbdd : BddAbove (Set.range v) := ⟨23 * I, by rintro _ ⟨γ, rfl⟩; exact hvb γ⟩
  have hwbdd : BddAbove (Set.range w) := ⟨31 * I, by rintro _ ⟨γ, rfl⟩; exact hwb γ⟩
  have hvne : (Set.range v).Nonempty := Set.range_nonempty v
  have hwne : (Set.range w).Nonempty := Set.range_nonempty w
  have hvs : sSup (Set.range v) ≤ 23 * I :=
    csSup_le hvne (by rintro _ ⟨γ, rfl⟩; exact hvb γ)
  have hws : sSup (Set.range w) ≤ 31 * I :=
    csSup_le hwne (by rintro _ ⟨γ, rfl⟩; exact hwb γ)
  obtain ⟨γ⟩ := ‹Nonempty Γ›
  have hvs0 : 0 ≤ sSup (Set.range v) :=
    le_trans (hv0 γ) (le_csSup hvbdd (Set.mem_range_self γ))
  have hws0 : 0 ≤ sSup (Set.range w) :=
    le_trans (hw0 γ) (le_csSup hwbdd (Set.mem_range_self γ))
  have hI0 : 0 ≤ I := by linarith [hw0 γ, hwb γ]
  refine ⟨hvbdd, hwbdd, hvs0, hvs, hws0, hws, ?_⟩
  calc
    _ ≤ (23 * I) * (31 * I) := mul_le_mul hvs hws hws0 (by positivity)
    _ = _ := by ring

end ThresholdHC.ResearchRouteA

#print axioms ThresholdHC.ResearchRouteA.separate_moment_bounds
#print axioms ThresholdHC.ResearchRouteA.uniform_family_bounds
