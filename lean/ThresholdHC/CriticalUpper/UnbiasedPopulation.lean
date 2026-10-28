import ThresholdHC.CriticalUpper.UnbiasedWork

/-! Integrability, exact mean, extended second moment and work in the actual population experiment. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem criticalUnbiased_population_integrable (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    Integrable ((criticalUnbiasedProcedure ρ).output ∘ populationInput
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q)
      (populationMeasure criticalGapLaw levelMeasure) := by
  let := criticalTapeLaw_probability q hq
  exact (populationInput_preserving criticalGapLaw levelMeasure _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq).integrable_comp_of_integrable
      ((criticalUnbiased_memLp ρ hρ hρ1 q hq hmass).integrable (by norm_num))

theorem criticalUnbiased_population_mean (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    populationMean criticalGapLaw levelMeasure
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q
      (criticalUnbiasedProcedure ρ) = ∫ d, (q d : ℝ) ∂criticalGapLaw := by
  have hp := populationInput_preserving criticalGapLaw levelMeasure _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq
  have hi := criticalUnbiased_mean ρ hρ hρ1 q hq hmass
  change (∫ z, (criticalUnbiasedProcedure ρ).output z ∂levelMeasure.prod
    (parameterTapeLaw (populationParameterLaw criticalGapLaw
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q))) = _ at hi
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable
    (criticalUnbiasedProcedure ρ).measurable_output.aestronglyMeasurable] at hi
  exact hi

theorem criticalUnbiased_population_second_moment (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    populationSecondMoment criticalGapLaw levelMeasure
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q
      (criticalUnbiasedProcedure ρ) ≤ ENNReal.ofReal (28*ρ) := by
  have hp := populationInput_preserving criticalGapLaw levelMeasure _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq
  have he := hp.lintegral_comp
    (ENNReal.measurable_ofReal.comp ((criticalUnbiasedProcedure ρ).measurable_output.pow_const 2))
  change populationSecondMoment criticalGapLaw levelMeasure
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q
      (criticalUnbiasedProcedure ρ) =
      ∫⁻ z, ENNReal.ofReal (((criticalUnbiasedProcedure ρ).output z)^2)
        ∂samplingMeasure (criticalTapeLaw q) at he
  rw [he,← ofReal_integral_eq_lintegral_ofReal
    (criticalUnbiased_memLp ρ hρ hρ1 q hq hmass).integrable_sq (ae_of_all _ (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (criticalUnbiased_second_moment ρ hρ hρ1 q hq hmass)

theorem criticalUnbiased_population_work (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    populationExpectedWork criticalGapLaw levelMeasure
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q
      (criticalUnbiasedProcedure ρ) ≤ ENNReal.ofReal (112000000*criticalLogFactor ρ) := by
  rw [populationInput_work criticalGapLaw levelMeasure _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq]
  exact criticalUnbiased_expected_work ρ hρ hρ1 q hq hmass

end ThresholdHC.CriticalUpper
