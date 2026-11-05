import ThresholdHC.ContinuousObserved.SampledCreation

noncomputable section
open MeasureTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

theorem state_population_parameter_law {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) :
    populationParameterLaw (volume : Measure unitInterval)
      (fun u => gapParameter false (D.gap u)) (fun u => gapParameter true (D.gap u)) (stateSignPrior D s) =
        volume.map (stateParameter D s) := by
  have : IsProbabilityMeasure
      (populationParameterLaw (volume : Measure unitInterval)
        (fun u => gapParameter false (D.gap u)) (fun u => gapParameter true (D.gap u)) (stateSignPrior D s)) :=
    populationParameterLaw_probability _ _ _ _
      ((measurable_gapParameter false).comp D.gap_measurable)
      ((measurable_gapParameter true).comp D.gap_measurable) (measurable_stateSignPrior D s)
  apply measure_eq_of_bounded_real_tests
  intro F hF hbound
  obtain ⟨C,hC⟩ := hbound
  rw [populationParameterLaw_integral (volume : Measure unitInterval)
      (fun u => gapParameter false (D.gap u)) (fun u => gapParameter true (D.gap u)) (stateSignPrior D s)
      ((measurable_gapParameter false).comp D.gap_measurable)
      ((measurable_gapParameter true).comp D.gap_measurable) (measurable_stateSignPrior D s) F hF C hC,
    integral_map (measurable_stateParameter D s).aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  cases hs : s (D.cell u) <;> simp [stateSignPrior,stateParameter,hs]

/-- After discarding the auxiliary outer-state sequence, sampled-state
queries have exactly the original population estimator's observable law. -/
theorem sampled_observable_law {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    P.map (fun z => (z.1.1,z.2)) =
      (experimentLaw μ A (conditionalSign μ D s)).map (fun z => (z.1.1,z.2)) := by
  have hr := sampled_creation_realizes D s A P hreal
  have h := population_simulation_observable_law A.randomLaw (volume : Measure unitInterval) P
    Prod.fst Prod.snd (fun u => gapParameter false (D.gap u)) (fun u => gapParameter true (D.gap u))
    (stateSignPrior D s) ((measurable_gapParameter false).comp D.gap_measurable)
    ((measurable_gapParameter true).comp D.gap_measurable) (measurable_stateSignPrior D s)
    (fun u => (D.gap u : ℝ)) (measurable_subtype_coe.comp D.gap_measurable)
    (fun u => ⟨(D.gap u).property.1.le,(D.gap u).property.2⟩)
    (ae_of_all _ (fun u => by simp [gapParameter,sub_eq_add_neg]))
    (ae_of_all _ (fun _ => rfl))
    A.policy A.policy_measurable measurable_fst measurable_snd hr
  rw [state_population_parameter_law,state_parameter_law μ D s hl] at h
  exact h.trans (original_observable_simulation_law μ A (conditionalSign μ D s)).symm

end ThresholdHC.ContinuousObserved
