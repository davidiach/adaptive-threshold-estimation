import ThresholdHC.ConfidenceLocalization.StatisticGeometry
import ThresholdHC.CriticalEntropy.PopulationTapeLaw
import ThresholdHC.CriticalEntropy.MidpointWork
import ThresholdHC.ObservableSimulation.LawUniqueness

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

/-- Midpoint regularization acts on the persistent coin parameter law. -/
theorem parameter_midpoint_law {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r) :
    populationParameterLaw μ p₀ p₁ (midpointPrior q r) =
      (1/2 : ℝ≥0) • populationParameterLaw μ p₀ p₁ q +
        (1/2 : ℝ≥0) • populationParameterLaw μ p₀ p₁ r := by
  let hprob (u : D → unitInterval) (hu : Measurable u) :=
    populationParameterLaw_probability μ p₀ p₁ u h₀ h₁ hu
  let := hprob q hq
  let := hprob r hr
  let := hprob (midpointPrior q r) (measurable_midpointPrior q r hq hr)
  apply measure_eq_of_bounded_real_tests
  intro F hF hbound
  obtain ⟨C,hC⟩ := hbound
  have hi (u : D → unitInterval) (hu : Measurable u) :
      Integrable F (populationParameterLaw μ p₀ p₁ u) := by
    let := hprob u hu
    exact ThresholdHC.Tier5.integrable_of_abs_bound _ _ hF C hC
  let f (u : D → unitInterval) (d : D) :=
    (u d : ℝ)*F (p₁ d)+(1-(u d : ℝ))*F (p₀ d)
  have hi' (u : D → unitInterval) (hu : Measurable u) : Integrable (f u) μ := by
    have hFm := hF.comp h₀
    have hFp := hF.comp h₁
    apply ThresholdHC.Tier5.integrable_of_abs_bound _ _ (by dsimp [f]; fun_prop) (2*C)
    intro d
    dsimp [f]
    have hp := (u d).property
    calc
      _ ≤ |(u d : ℝ)*F (p₁ d)| + |(1-(u d : ℝ))*F (p₀ d)| := abs_add_le _ _
      _ ≤ C+C := add_le_add
        (by rw [abs_mul,abs_of_nonneg hp.1]
            exact (mul_le_of_le_one_left (abs_nonneg _) hp.2).trans (hC _))
        (by rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hp.2)]
            exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hp.1])).trans (hC _))
      _ = _ := by ring
  rw [integral_add_measure (hi q hq).smul_measure_nnreal (hi r hr).smul_measure_nnreal,
    integral_smul_nnreal_measure,integral_smul_nnreal_measure]
  simp only [NNReal.smul_def,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one,smul_eq_mul]
  rw [populationParameterLaw_integral μ p₀ p₁ _ h₀ h₁ (measurable_midpointPrior q r hq hr) F hF C hC,
    populationParameterLaw_integral μ p₀ p₁ q h₀ h₁ hq F hF C hC,
    populationParameterLaw_integral μ p₀ p₁ r h₀ h₁ hr F hF C hC]
  change (∫ d, f (midpointPrior q r) d ∂μ) =
    1/2*(∫ d, f q d ∂μ)+1/2*(∫ d, f r d ∂μ)
  rw [← integral_const_mul,← integral_const_mul,← integral_add ((hi' q hq).const_mul _) ((hi' r hr).const_mul _)]
  apply integral_congr_ae
  exact ae_of_all _ (fun d => by dsimp [f,midpointPrior]; ring)

end ThresholdHC.ConfidenceLocalization
