import ThresholdHC.ContinuousObserved.UniformUpper
noncomputable section
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState
open ThresholdHC.ContinuousObserved ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    μ.withDensity (fun d => ENNReal.ofReal ((conditionalSign μ D s).val d)) = positiveGapLaw D s :=
  conditionalSign_density μ D s hl

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ)
    (F : Gap → ℝ) (hF : Measurable F) :
    (∫ d, (conditionalSign μ D s).val d * F d ∂μ) =
      ∫ u in {u : unitInterval | s (D.cell u) = true}, F (D.gap u) :=
  conditionalSign_positive_integral μ D s hl F hF

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    volume.map (stateParameter D s) =
      populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit (conditionalSign μ D s)) :=
  state_parameter_law μ D s hl

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    signMean μ (conditionalSign μ D s).val = stateTarget D.cell s := conditionalSign_target μ D s hl

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) :
    (sampledStateEstimator A).randomLaw = A.randomLaw.prod outerSequenceLaw := rfl

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (z : (R × (ℕ → unitInterval)) × ProcessTape) :
    (sampledStateEstimator A).output z = A.output (z.1.1,z.2) := rfl

example {n : ℕ} (pol : List Bool → Option ℕ) (d : ℕ → ℝ) (s : ℕ → Bool) (w : Prefix n) :
    ThresholdHC.Tier5.creationLaw pol d (fun i => if s i then 1 else 0) w =
      countablePath pol (fun i => 1 / 2 + (if s i then d i else -d i)) w := deterministic_creation pol d s w

example (pol : List Bool → Option ℕ) (p : ℕ → unitInterval) (n : ℕ) (F : Prefix n → ℝ≥0∞) :
    countableExpectation pol p n F =
      ∑ w, ENNReal.ofReal (countablePath pol (fun i => (p i : ℝ)) w) * F w := countableExpectation_sum pol p n F

example {R W : Type} [MeasurableSpace R] [MeasurableSpace W] [Fintype W] [MeasurableSingletonClass W]
    (μ : Measure R) (P : Measure (R × W)) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (p : R → W → ℝ) (hp : ∀ w, Measurable (fun r => p r w))
    (hp0 : ∀ r w, 0 ≤ p r w) (hs : ∀ r, (∑ w, p r w) = 1)
    (hl : ∀ F : R × W → ℝ≥0∞, Measurable F →
      (∫⁻ z, F z ∂P) = ∫⁻ r, ∑ w, ENNReal.ofReal (p r w) * F (r,w) ∂μ) :
    ThresholdHC.Tier5.FiniteKernelRealization μ P p := finite_kernel_of_lintegral μ P p hp hp0 hs hl

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (s : Fin N → Bool) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    ThresholdHC.Tier5.RealizesCreationPrefixes (A.randomLaw.prod outerSequenceLaw) P Prod.fst Prod.snd
      (sampledPolicy A) (sampledGap D) (sampledPrior D s) := sampled_creation_realizes D s A P hreal

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    P.map (fun z => (z.1.1,z.2)) =
      (experimentLaw μ A (conditionalSign μ D s)).map (fun z => (z.1.1,z.2)) :=
  sampled_observable_law μ D s hl A P hreal

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    (∫⁻ z, totalProcessWork z.2 ∂P) = ThresholdHC.Tier6.expectedWork μ A (conditionalSign μ D s) :=
  sampled_expectedWork μ D s hl A P hreal

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    squaredRisk P (sampledStateEstimator A).output (stateTarget D.cell s) =
      squaredRisk (experimentLaw μ A (conditionalSign μ D s)) (populationOutput A)
        (signMean μ (conditionalSign μ D s).val) := sampled_squaredRisk μ D s hl A P hreal

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    rootMeanRisk P (sampledStateEstimator A).output (stateTarget D.cell s) =
      rootMeanRisk (experimentLaw μ A (conditionalSign μ D s)) (populationOutput A)
        (signMean μ (conditionalSign μ D s).val) := sampled_rootMeanRisk μ D s hl A P hreal

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) (r : ℝ) :
    P {z | r < |(sampledStateEstimator A).output z - stateTarget D.cell s|} =
      ThresholdHC.Confidence.failureProbability μ A (conditionalSign μ D s) r :=
  sampled_failureProbability μ D s hl A P hreal r

example (B : ℝ) (hB : 1 ≤ B) {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ)
    (P : Measure ((ThresholdHC.BlindUpper.BatchSeed × (ℕ → unitInterval)) × ProcessTape))
    [IsProbabilityMeasure P] (hreal : RealizesQueryPrefixes D (rmsStateEstimator B) s P) :
    (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal B ∧
      rootMeanRisk P (rmsStateEstimator B).output (stateTarget D.cell s) ≤
        ENNReal.ofReal (512 * modulus μ (1 / Real.sqrt B)) := observed_rms_upper B hB μ D s hl P hreal

example :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → StateEstimator R),
      ∀ B δ : ℝ, 1 ≤ B → 0 < δ → δ ≤ 1 / 4 →
        ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool),
          volume.map D.gap = μ →
          ∀ (P : Measure (R × ProcessTape)) [IsProbabilityMeasure P],
            RealizesQueryPrefixes D (rule B δ) s P →
            (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal B ∧
              P {z | 8192 * modulus μ (ThresholdHC.Confidence.confidenceScale B δ) <
                |(rule B δ).output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ := observed_confidence_upper

example (ε : ℝ) :
    uniformUpperBudget ε = (131072 : ℝ) ^ 2 * (ε ^ 2)⁻¹ * (Real.log (1 / ε)) ^ 2 * Real.log 16 :=
  uniformUpperBudget_eq ε

example {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.exp (-16)) :
    1 ≤ uniformUpperBudget ε ∧
      8192 * modulus uniformGaps (ThresholdHC.Confidence.confidenceScale (uniformUpperBudget ε) (1 / 16)) ≤ ε ∧
      512 * modulus uniformGaps (1 / Real.sqrt (uniformUpperBudget ε)) ≤ ε := uniform_upper_radius hε he

example :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → StateEstimator R),
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-16) →
        ∀ (N : ℕ) (D : QueryDesign N) (s : Fin N → Bool), volume.map D.gap = uniformGaps →
          ∀ (P : Measure (R × ProcessTape)) [IsProbabilityMeasure P],
            RealizesQueryPrefixes D (rule ε) s P →
            (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal (uniformUpperBudget ε) ∧
              P {z | ε < |(rule ε).output z - stateTarget D.cell s|} ≤ ENNReal.ofReal (1 / 16) :=
  uniform_observed_confidence_upper

example {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.exp (-16)) {N : ℕ}
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = uniformGaps)
    (P : Measure ((ThresholdHC.BlindUpper.BatchSeed × (ℕ → unitInterval)) × ProcessTape))
    [IsProbabilityMeasure P] (hreal : RealizesQueryPrefixes D (rmsStateEstimator (uniformUpperBudget ε)) s P) :
    (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal (uniformUpperBudget ε) ∧
      rootMeanRisk P (rmsStateEstimator (uniformUpperBudget ε)).output (stateTarget D.cell s) ≤ ENNReal.ofReal ε :=
  uniform_observed_rms_upper hε he D s hl P hreal
#print axioms ThresholdHC.ContinuousObserved.capped_path
#print axioms ThresholdHC.ContinuousObserved.conditionalSign_density
#print axioms ThresholdHC.ContinuousObserved.conditionalSign_positive_integral
#print axioms ThresholdHC.ContinuousObserved.conditionalSign_target
#print axioms ThresholdHC.ContinuousObserved.countableExpectation_sum
#print axioms ThresholdHC.ContinuousObserved.countablePath_cons
#print axioms ThresholdHC.ContinuousObserved.countablePath_initial_stop
#print axioms ThresholdHC.ContinuousObserved.countablePath_nonneg
#print axioms ThresholdHC.ContinuousObserved.deterministic_creation
#print axioms ThresholdHC.ContinuousObserved.deterministic_sign_weight
#print axioms ThresholdHC.ContinuousObserved.deterministic_transcript
#print axioms ThresholdHC.ContinuousObserved.finite_kernel_of_lintegral
#print axioms ThresholdHC.ContinuousObserved.measurable_sampledGap
#print axioms ThresholdHC.ContinuousObserved.measurable_sampledPolicy
#print axioms ThresholdHC.ContinuousObserved.measurable_sampledPrior
#print axioms ThresholdHC.ContinuousObserved.measurable_stateParameter
#print axioms ThresholdHC.ContinuousObserved.measurable_stateSignPrior
#print axioms ThresholdHC.ContinuousObserved.observed_confidence_upper
#print axioms ThresholdHC.ContinuousObserved.observed_rms_upper
#print axioms ThresholdHC.ContinuousObserved.outerSequenceLaw_probability
#print axioms ThresholdHC.ContinuousObserved.positiveGapLaw_finite
#print axioms ThresholdHC.ContinuousObserved.positiveGapLaw_le
#print axioms ThresholdHC.ContinuousObserved.positiveState_measurable
#print axioms ThresholdHC.ContinuousObserved.sampledGap_range
#print axioms ThresholdHC.ContinuousObserved.sampledPrior_range
#print axioms ThresholdHC.ContinuousObserved.sampledStateEstimator
#print axioms ThresholdHC.ContinuousObserved.sampled_creation_realizes
#print axioms ThresholdHC.ContinuousObserved.sampled_expectedWork
#print axioms ThresholdHC.ContinuousObserved.sampled_failureProbability
#print axioms ThresholdHC.ContinuousObserved.sampled_lintegral
#print axioms ThresholdHC.ContinuousObserved.sampled_observable_law
#print axioms ThresholdHC.ContinuousObserved.sampled_prefix_creation_sum
#print axioms ThresholdHC.ContinuousObserved.sampled_rootMeanRisk
#print axioms ThresholdHC.ContinuousObserved.sampled_squaredRisk
#print axioms ThresholdHC.ContinuousObserved.sampling_prefix_expectation
#print axioms ThresholdHC.ContinuousObserved.stateSignPrior_coe
#print axioms ThresholdHC.ContinuousObserved.state_parameter_law
#print axioms ThresholdHC.ContinuousObserved.state_population_parameter_law
#print axioms ThresholdHC.ContinuousObserved.uniformUpperBudget_eq
#print axioms ThresholdHC.ContinuousObserved.uniform_observed_confidence_upper
#print axioms ThresholdHC.ContinuousObserved.uniform_observed_rms_upper
#print axioms ThresholdHC.ContinuousObserved.uniform_upper_radius
