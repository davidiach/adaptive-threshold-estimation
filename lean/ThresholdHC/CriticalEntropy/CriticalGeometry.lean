import ThresholdHC.CriticalEntropy.HellingerGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- The compact model represents exactly the actual admissible populations,
up to almost-everywhere equality, and retains their true target integrals. -/
theorem critical_population_representation (ρ : ℝ) (hρ : 0 ≤ ρ) :
    IsCompact (populationDualSet criticalGapLaw ρ) ∧
    Convex ℝ (populationDualSet criticalGapLaw ρ) ∧
    (populationDualSet criticalGapLaw ρ).Nonempty ∧
    (∀ f ∈ populationDualSet criticalGapLaw ρ,
      CappedPrior criticalGapLaw ρ (populationDualPrior criticalGapLaw f) ∧
      populationTarget criticalGapLaw f =
        ∫ d, (populationDualPrior criticalGapLaw f d : ℝ) ∂criticalGapLaw) ∧
    (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw ρ q →
      ∃ f ∈ populationDualSet criticalGapLaw ρ,
        (fun d => (populationDualPrior criticalGapLaw f d : ℝ)) =ᵐ[criticalGapLaw]
          (fun d => (q d : ℝ))) := by
  refine ⟨populationDualSet_compact _ _,populationDualSet_convex _ _,
    populationDualSet_nonempty _ _ hρ,?_,?_⟩
  · intro f hf
    exact ⟨populationDualPrior_admissible _ _ f hf,
      (populationDualPrior_mass _ _ f hf).symm⟩
  · intro q hq
    exact populationDualSet_covers_priors _ _ q hq.1 hq.2.1 hq.2.2

/-- The finite image includes a separate target coordinate. Active observation
coordinates have a uniform positive lower bound over the whole population class. -/
theorem critical_observation_geometry {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∃ F : PopulationDual criticalGapLaw →ᵃ[ℝ] (Option (Fin (m+1) × Fin (m+1)) → ℝ),
      Continuous F ∧ ∀ f ∈ populationDualSet criticalGapLaw ρ,
        F f = cappedObservationVector criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true)
          (populationDualPrior criticalGapLaw f) A m) ∧
    IsCompact (cappedObservationImage criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ) ∧
    Convex ℝ (cappedObservationImage criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ) ∧
    (cappedObservationImage criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ).Nonempty ∧
    (∀ i : Fin (m+1) × Fin (m+1),
      ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)) {i} ≠ 0 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ cappedObservationImage criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ,
        ε ≤ v (some i)) := by
  obtain ⟨hc,hv⟩ := capped_observation_image_compact_convex criticalGapLaw ν _ _
    (measurable_criticalParameter false) (measurable_criticalParameter true) A m hcap ρ
  refine ⟨capped_observation_affine_representation criticalGapLaw ν _ _
    (measurable_criticalParameter false) (measurable_criticalParameter true) A m hcap ρ,
    hc,hv,capped_observation_image_nonempty _ _ _ _ _ _ _ hρ,?_⟩
  intro i hi
  exact capped_observation_uniform_positive criticalGapLaw ν _ _
    (measurable_criticalParameter false) (measurable_criticalParameter true)
    A m hcap ρ hρ critical_parameters_interior i hi

theorem populationPairSet_realization {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ δ : ℝ)
    (z : PopulationDual μ × PopulationDual μ) (hz : z ∈ populationPairSet μ ρ δ) :
    CappedPrior μ ρ (populationDualPrior μ z.1) ∧
    CappedPrior μ ρ (populationDualPrior μ z.2) ∧
    δ ≤ (∫ d, (populationDualPrior μ z.2 d : ℝ) ∂μ) -
      (∫ d, (populationDualPrior μ z.1 d : ℝ) ∂μ) := by
  refine ⟨populationDualPrior_admissible μ ρ z.1 hz.1.1,
    populationDualPrior_admissible μ ρ z.2 hz.1.2,?_⟩
  rw [populationDualPrior_mass μ ρ z.2 hz.1.2,populationDualPrior_mass μ ρ z.1 hz.1.1]
  exact hz.2

/-- The separated pair set is compact, convex and nonempty before any policy
is chosen. Each actual capped experiment supplies a continuous convex distance
on this same set. This does not assert a simultaneously hard pair. -/
theorem critical_pair_hellinger_geometry (ρ δ : ℝ)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2) (hδρ : δ ≤ ρ) :
    IsCompact (populationPairSet criticalGapLaw ρ δ) ∧
    Convex ℝ (populationPairSet criticalGapLaw ρ δ) ∧
    (populationPairSet criticalGapLaw ρ δ).Nonempty ∧
    (∀ z ∈ populationPairSet criticalGapLaw ρ δ,
      CappedPrior criticalGapLaw ρ (populationDualPrior criticalGapLaw z.1) ∧
      CappedPrior criticalGapLaw ρ (populationDualPrior criticalGapLaw z.2) ∧
      δ ≤ (∫ d, (populationDualPrior criticalGapLaw z.2 d : ℝ) ∂criticalGapLaw) -
        (∫ d, (populationDualPrior criticalGapLaw z.1 d : ℝ) ∂criticalGapLaw)) ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) →
      ∃ H : PopulationDual criticalGapLaw × PopulationDual criticalGapLaw → ℝ,
        Continuous H ∧ ConvexOn ℝ (populationPairSet criticalGapLaw ρ δ) H ∧
        ∀ z ∈ populationPairSet criticalGapLaw ρ δ,
          H z = 1-(hellingerAffinity
            (cappedTranscriptLaw criticalGapLaw ν
              (fun d => criticalParameter d false) (fun d => criticalParameter d true)
              (populationDualPrior criticalGapLaw z.1) A m)
            (cappedTranscriptLaw criticalGapLaw ν
              (fun d => criticalParameter d false) (fun d => criticalParameter d true)
              (populationDualPrior criticalGapLaw z.2) A m)).toReal ∧ H z ∈ Icc 0 1 := by
  obtain ⟨hc,hv⟩ := populationPairSet_compact_convex criticalGapLaw ρ δ
  refine ⟨hc,hv,populationPairSet_nonempty _ _ _ hδ hδhalf hδρ,
    populationPairSet_realization _ _ _,?_⟩
  intro R E _ _ ν _ A m hcap
  obtain ⟨H,hHc,hHv,hH⟩ := capped_observation_hellinger_geometry criticalGapLaw ν _ _
    (measurable_criticalParameter false) (measurable_criticalParameter true)
    A m hcap ρ critical_parameters_interior
  refine ⟨H,hHc,hHv.subset (fun z hz => hz.1) hv,?_⟩
  intro z hz
  have he := hH z.1 hz.1.1 z.2 hz.1.2
  refine ⟨he,?_⟩
  rw [he]
  have hb := capped_observation_affinity_le_one criticalGapLaw ν _ _
    (populationDualPrior criticalGapLaw z.1) (populationDualPrior criticalGapLaw z.2)
    (measurable_criticalParameter false) (measurable_criticalParameter true)
    (populationDualPrior_measurable _ _) (populationDualPrior_measurable _ _)
    A m hcap critical_parameters_interior
  have hr := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hb
  have hn := ENNReal.toReal_nonneg (a := hellingerAffinity
    (cappedTranscriptLaw criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true)
      (populationDualPrior criticalGapLaw z.1) A m)
    (cappedTranscriptLaw criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true)
      (populationDualPrior criticalGapLaw z.2) A m))
  simp only [ENNReal.toReal_one] at hr
  exact ⟨by linarith,by linarith⟩

end ThresholdHC.CriticalEntropy
