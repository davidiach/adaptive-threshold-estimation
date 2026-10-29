import ThresholdHC.RareAboveTwo.Execution
import ThresholdHC.RareAboveTwo.UnbiasedWork
import ThresholdHC.BlindUpper.CallLaw

/-! Transfer to the original infinite adaptive experiment, with actual work. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem call_projection_preserving (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a ρ : ℝ) :
    MeasurePreserving (fun z : ℕ × (ℕ → ℕ → Bool) => (z.1,z.2 0))
      (originalSimulationLaw μ (observableEstimator a ρ) q) (callMeasure μ q) :=
  (MeasurePreserving.id levelMeasure).prod
    (measurePreserving_eval_infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) 0)

theorem output_lintegral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a ρ : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (populationOutput (observableEstimator a ρ) z) ∂experimentLaw μ (observableEstimator a ρ) q) =
      ∫⁻ z, F (callValue a ρ z) ∂callMeasure μ q := by
  have he := original_observable_lintegral μ (observableEstimator a ρ) q (F ∘ output a ρ)
    (hF.comp (measurable_output a ρ))
  change _ = ∫⁻ z, F (output a ρ (z.1,populationPath (policy a ρ z.1) z.2))
    ∂originalSimulationLaw μ (observableEstimator a ρ) q at he
  simp_rw [population_output] at he
  exact he.trans ((call_projection_preserving μ q a ρ).lintegral_comp (hF.comp (measurable_callValue a ρ)))

theorem output_law (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a ρ : ℝ) :
    (experimentLaw μ (observableEstimator a ρ) q).map (populationOutput (observableEstimator a ρ)) =
      (callMeasure μ q).map (callValue a ρ) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_populationOutput (observableEstimator a ρ)),
    lintegral_map hF (measurable_callValue a ρ)]
  exact output_lintegral μ q a ρ F hF

theorem expectedWork_eq (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a ρ : ℝ) :
    expectedWork μ (observableEstimator a ρ) q =
      ∫⁻ z, stoppedProcedureWork (rareUnbiasedProcedure a ρ) z ∂samplingMeasure (originalPopulationTapeLaw μ q) := by
  rw [original_expectedWork_simulation]
  change (∫⁻ z, totalProcessWork (populationPath (policy a ρ z.1) z.2)
    ∂originalSimulationLaw μ (observableEstimator a ρ) q) = _
  simp_rw [population_work]
  have he := (call_projection_preserving μ q a ρ).lintegral_comp
    ((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (measurable_callCost a ρ))
  simp only [Function.comp_apply] at he
  rw [he]
  change (∫⁻ z, (callCost a ρ z : ℝ≥0∞) ∂samplingMeasure (originalPopulationTapeLaw μ q)) = _
  apply lintegral_congr
  intro z
  simp [rareUnbiasedProcedure_work,callCost]

theorem output_second_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    (∫⁻ z, ENNReal.ofReal ((populationOutput (observableEstimator a ρ) z)^2)
      ∂experimentLaw μ (observableEstimator a ρ) q) ≤ ENNReal.ofReal (28*ρ) := by
  rw [output_lintegral μ q a ρ (fun x : ℝ => ENNReal.ofReal (x^2)) (measurable_id.pow_const 2).ennreal_ofReal]
  change (∫⁻ z, ENNReal.ofReal (((rareUnbiasedProcedure a ρ).output z)^2)
    ∂samplingMeasure (originalPopulationTapeLaw μ q)) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (rareUnbiased_memLp μ α a ρ hα ha ha' hρ hρ1 hm q hq).integrable_sq
    (ae_of_all _ (fun z => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (rareUnbiased_second_moment μ α a ρ hα ha ha' hρ hρ1 hm q hq)

theorem output_memLp (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    MemLp (populationOutput (observableEstimator a ρ)) 2 (experimentLaw μ (observableEstimator a ρ) q) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_populationOutput (observableEstimator a ρ)).aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_populationOutput (observableEstimator a ρ)).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun z => sq_nonneg _))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (output_second_moment μ α a ρ hα ha ha' hρ hρ1 hm q hq)

theorem output_mean (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) :
    (∫ z, populationOutput (observableEstimator a ρ) z ∂experimentLaw μ (observableEstimator a ρ) q) =
      signMean μ q.val := by
  have ho := measurable_populationOutput (observableEstimator a ρ)
  calc
    _ = ∫ x : ℝ, x ∂(experimentLaw μ (observableEstimator a ρ) q).map
        (populationOutput (observableEstimator a ρ)) :=
      (integral_map ho.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ z, callValue a ρ z ∂callMeasure μ q := by
      rw [output_law]
      exact integral_map (measurable_callValue a ρ).aemeasurable measurable_id.aestronglyMeasurable
    _ = _ := rareUnbiased_mean μ α a ρ hα ha ha' hρ hρ1 hm q hq

end ThresholdHC.RareAboveTwo
