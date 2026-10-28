import ThresholdHC.Observable713.Execution
import ThresholdHC.Observable713.Population

/-! Transfer the call law to the original adaptive experiment, including actual work. -/

noncomputable section
namespace ThresholdHC.Observable713
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem call_projection_preserving (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    MeasurePreserving (fun z : ℕ × (ℕ → ℕ → Bool) => (z.1,z.2 0))
      (originalSimulationLaw μ observableEstimator q) (callMeasure μ q) :=
  (MeasurePreserving.id levelMeasure).prod
    (measurePreserving_eval_infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) 0)

theorem output_lintegral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (populationOutput observableEstimator z) ∂experimentLaw μ observableEstimator q) =
      ∫⁻ z, F (callValue z) ∂callMeasure μ q := by
  have he := original_observable_lintegral μ observableEstimator q (F ∘ output)
    (hF.comp measurable_output)
  change _ = ∫⁻ z, F (output (z.1,populationPath (policy z.1) z.2))
    ∂originalSimulationLaw μ observableEstimator q at he
  simp_rw [population_output] at he
  exact he.trans ((call_projection_preserving μ q).lintegral_comp (hF.comp measurable_callValue))

theorem output_law (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (experimentLaw μ observableEstimator q).map (populationOutput observableEstimator) =
      (callMeasure μ q).map callValue := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_populationOutput observableEstimator),
    lintegral_map hF measurable_callValue]
  exact output_lintegral μ q F hF

theorem expectedWork_eq (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    expectedWork μ observableEstimator q = ∫⁻ z, (callCost z : ℝ≥0∞) ∂callMeasure μ q := by
  rw [original_expectedWork_simulation]
  change (∫⁻ z, totalProcessWork (populationPath (policy z.1) z.2)
    ∂originalSimulationLaw μ observableEstimator q) = _
  simp_rw [population_work]
  exact (call_projection_preserving μ q).lintegral_comp
    ((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp measurable_callCost)

theorem output_memLp (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    MemLp (populationOutput observableEstimator) 2 (experimentLaw μ observableEstimator q) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_populationOutput observableEstimator).aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_populationOutput observableEstimator).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun z => sq_nonneg _))).mp
  rw [output_lintegral μ q (fun x : ℝ => ENNReal.ofReal (x^2))
    (measurable_id.pow_const 2).ennreal_ofReal]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (call_second_le μ q hI)

theorem output_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    (∫ z, populationOutput observableEstimator z ∂experimentLaw μ observableEstimator q) =
      signMean μ q.val := by
  have hm := measurable_populationOutput observableEstimator
  calc
    _ = ∫ x : ℝ, x ∂(experimentLaw μ observableEstimator q).map
        (populationOutput observableEstimator) :=
      (integral_map hm.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ z, callValue z ∂callMeasure μ q := by
      rw [output_law]
      exact integral_map measurable_callValue.aemeasurable measurable_id.aestronglyMeasurable
    _ = _ := call_mean μ q hI

theorem output_variance_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    evariance (populationOutput observableEstimator) (experimentLaw μ observableEstimator q) ≤
      ENNReal.ofReal (23*∫ d : Gap, (d : ℝ)⁻¹ ∂μ) := by
  rw [← ofReal_variance (output_memLp μ q hI)]
  calc
    _ ≤ ENNReal.ofReal (∫ z, (populationOutput observableEstimator z)^2
        ∂experimentLaw μ observableEstimator q) :=
      ENNReal.ofReal_le_ofReal (variance_le_expectation_sq
        (measurable_populationOutput observableEstimator).aestronglyMeasurable)
    _ = ∫⁻ z, ENNReal.ofReal ((populationOutput observableEstimator z)^2)
        ∂experimentLaw μ observableEstimator q :=
      ofReal_integral_eq_lintegral_ofReal (output_memLp μ q hI).integrable_sq
        (ae_of_all _ (fun z => sq_nonneg _))
    _ = ∫⁻ z, ENNReal.ofReal ((callValue z)^2) ∂callMeasure μ q :=
      output_lintegral μ q (fun x : ℝ => ENNReal.ofReal (x^2))
        (measurable_id.pow_const 2).ennreal_ofReal
    _ ≤ _ := call_second_le μ q hI

end ThresholdHC.Observable713
