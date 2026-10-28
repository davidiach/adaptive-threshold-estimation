import ThresholdHC.CriticalUpper.CoupledModel
import ThresholdHC.CriticalEntropy.PopulationLocalWork

/-! The actual mixture tape law, population transfer and classifier bias. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

def criticalTapeLaw (q : ℝ → unitInterval) : Measure (ℕ → Bool) :=
  parameterTapeLaw (populationParameterLaw criticalGapLaw
    (fun d => criticalParameter d false) (fun d => criticalParameter d true) q)

theorem criticalTapeLaw_probability (q : ℝ → unitInterval) (hq : Measurable q) :
    IsProbabilityMeasure (criticalTapeLaw q) := by
  let := populationParameterLaw_probability criticalGapLaw _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq
  exact parameterTapeLaw_probability _

theorem criticalTapeLaw_preserving (q : ℝ → unitInterval) (hq : Measurable q) :
    MeasurePreserving
      (fun z => (populationInput (R := Unit) (fun d => criticalParameter d false)
        (fun d => criticalParameter d true) q z).2)
      (populationMeasure criticalGapLaw (Measure.dirac ())) (criticalTapeLaw q) := by
  let := criticalTapeLaw_probability q hq
  exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := criticalTapeLaw q)).comp
    (populationInput_preserving criticalGapLaw (Measure.dirac ()) _ _ q
      (measurable_criticalParameter false) (measurable_criticalParameter true) hq)

theorem criticalTapeLaw_integral (q : ℝ → unitInterval) (hq : Measurable q)
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) :
    (∫ ω, F ω ∂criticalTapeLaw q) =
      ∫ z, F ((populationInput (R := Unit) (fun d => criticalParameter d false)
        (fun d => criticalParameter d true) q z).2)
        ∂populationMeasure criticalGapLaw (Measure.dirac ()) := by
  have hp := criticalTapeLaw_preserving q hq
  rw [← hp.map_eq]
  exact integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable

theorem integral_dirac_unit_tape (F : (ℕ → Bool) → ℝ) (hF : Measurable F)
    (M : ℝ) (hbound : ∀ ω, |F ω| ≤ M) (p : unitInterval) :
    (∫ z : Unit × (ℕ → Bool), F z.2 ∂(Measure.dirac ()).prod (Tier2.tapeMeasure p)) =
      ∫ ω, F ω ∂Tier2.tapeMeasure p := by
  have hi : Integrable (fun z : Unit × (ℕ → Bool) => F z.2)
      ((Measure.dirac ()).prod (Tier2.tapeMeasure p)) := by
    apply Integrable.of_bound (hF.comp measurable_snd).aestronglyMeasurable M
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound z.2)
  rw [integral_prod _ hi]
  simp

theorem criticalTapeLaw_integral_mixture (q : ℝ → unitInterval) (hq : Measurable q)
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ ω, |F ω| ≤ M) :
    (∫ ω, F ω ∂criticalTapeLaw q) =
      ∫ d, (q d : ℝ)*(∫ ω, F ω ∂Tier2.tapeMeasure (criticalParameter d true))+
        (1-(q d : ℝ))*(∫ ω, F ω ∂Tier2.tapeMeasure (criticalParameter d false)) ∂criticalGapLaw := by
  rw [criticalTapeLaw_integral q hq F hF]
  have hm := (hF.comp measurable_snd).comp
    (measurable_populationInput (R := Unit) _ _ q
      (measurable_criticalParameter false) (measurable_criticalParameter true) hq)
  have hi : Integrable (fun z => F ((populationInput (R := Unit)
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q z).2))
      (criticalGapLaw.prod (uniformUnitMeasure.prod ((Measure.dirac ()).prod uniformTapeMeasure))) := by
    apply Integrable.of_bound hm.aestronglyMeasurable M
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound _)
  unfold populationMeasure
  rw [population_integral criticalGapLaw (Measure.dirac ()) _ _ q
    (fun z => F z.2) (hF.comp measurable_snd) hi]
  simp_rw [integral_dirac_unit_tape F hF M hbound]

theorem calibratedValue_integrable (ρ : ℝ) (j : ℕ) (q : ℝ → unitInterval) (hq : Measurable q) :
    Integrable (calibratedValue ρ j) (criticalTapeLaw q) := by
  let := criticalTapeLaw_probability q hq
  exact integrable_binary (measurable_calibratedValue ρ j) (calibratedValue_binary ρ j)

theorem calibratedValue_population_mean (ρ : ℝ) (j : ℕ) (q : ℝ → unitInterval) (hq : Measurable q) :
    (∫ ω, calibratedValue ρ j ω ∂criticalTapeLaw q) =
      populationMean criticalGapLaw (Measure.dirac ())
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q (calibratedScreen ρ j) := by
  rw [criticalTapeLaw_integral q hq _ (measurable_calibratedValue ρ j)]
  rfl

theorem calibratedValue_bias (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    |(∫ ω, calibratedValue ρ j ω ∂criticalTapeLaw q)-(∫ d, (q d : ℝ) ∂criticalGapLaw)| ≤
      3*ρ*screenAccuracy j := by
  rw [calibratedValue_population_mean ρ j q hq]
  exact (screen_population_bias_le _ _ _ q hq).trans (calibratedScreen_error ρ hρ hρ1 j q hq hmass)

end ThresholdHC.CriticalUpper
