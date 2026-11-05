import ThresholdHC.ContinuousObserved.QueryLower
import ThresholdHC.ContinuousObserved.Regularity
import ThresholdHC.ContinuousObserved.UniformRMSLower
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6
open ThresholdHC.ObservedState ThresholdHC.ContinuousObserved
open ThresholdHC.CriticalEntropy

example (g : List Bool → Bool → Bool) (x : ProcessTape) (n : ℕ) :
    processHistory (decodeTape g x) n = decode g (processHistory x n) :=
  decodeTape_history g x n

example (g : List Bool → Bool → Bool) (x : ProcessTape) :
    totalProcessWork (decodeTape g x) = totalProcessWork x := decodeTape_work g x

example (b d : Gap) (hd : (d : ℝ) ≤ b) (s : Bool) :
    ((bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s b)).prod uniformUnitMeasure).map
      (fun z => Bool.xor z.1 (uniformCoinFlip (noiseRate b d hd) z.2)) =
        bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d) :=
  uniform_garbling_law b d hd s

example :
    MeasurePreserving (fun v : ℕ → ℝ => (v 0,uniformTail v)) uniformTapeMeasure
      (uniformUnitMeasure.prod uniformTapeMeasure) := uniform_head_tail_preserving

example {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (s : Fin N → Bool) : IsProbabilityMeasure (queryLaw D A s) := queryLaw_probability D A s

example {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (s : Fin N → Bool) :
    (∫⁻ z, totalProcessWork z.2 ∂queryLaw D A s) =
      ThresholdHC.ObservedState.expectedWork (reduction D A) D.cap s := reduction_work D A s

example {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (s : Fin N → Bool) (r θ : ℝ) :
    queryLaw D A s {z | r < |A.output z - θ|} =
      modelLaw (reduction D A) D.cap s {z | r < |(reduction D A).output z - θ|} :=
  reduction_error D A s r θ

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) (D : CellDesign μ h δ)
    {R : Type} [MeasurableSpace R] (A : StateEstimator R) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ s, (∫⁻ z, totalProcessWork z.2 ∂queryLaw (CellDesign.queryDesign μ h δ D) A s) ≤ ENNReal.ofReal B)
    (hc : ∀ s, queryLaw (CellDesign.queryDesign μ h δ D) A s
      {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) :
    (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B :=
  simulated_confidence_lower μ h hδ hd D A hB hw hc

example {N : ℕ} (D : QueryDesign N) (c : List Bool → Bool)
    (q : List Bool → unitInterval) (n : ℕ) (v : ℕ → ℝ) (raw : Fin N → ℕ → Bool) :
    noisyWord D c q n v raw =
      decodePrefix (stepNoise D q v) (populationSimulation (rawPolicy D c q v) n raw).2 :=
  noisyWord_decode D c q n v raw

example {N : ℕ} (cap : Fin N → Gap) (s : Fin N → Bool)
    (j : Fin N) (d : Gap) (hd : (d : ℝ) ≤ cap j) :
    MeasurePreserving
      (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
        (Bool.xor (z.2 j 0) (uniformCoinFlip (noiseRate (cap j) d hd) (z.1 0)),
          (uniformTail z.1,Function.update z.2 j (tapeDrop 1 (z.2 j)))))
      (uniformTapeMeasure.prod (Measure.pi (fun i =>
        Tier2.tapeMeasure (ThresholdHC.ObservableSimulation.gapParameter (s i) (cap i)))))
      ((bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter (s j) d)).prod
        (uniformTapeMeasure.prod (Measure.pi (fun i =>
          Tier2.tapeMeasure (ThresholdHC.ObservableSimulation.gapParameter (s i) (cap i)))))) :=
  fresh_observation_preserving cap s j d hd

example {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (c : List Bool → Bool) (q : List Bool → unitInterval) (n : ℕ) (F : Prefix n → ℝ≥0∞) :
    (∫⁻ z, F (noisyWord D c q n z.1 z.2)
      ∂uniformTapeMeasure.prod (Measure.pi (fun i =>
        Tier2.tapeMeasure (ThresholdHC.ObservableSimulation.gapParameter (s i) (D.cap i))))) =
        prefixExpectation D s c q n F := noisyWord_prefix_law D s c q n F

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool) :
    RealizesQueryPrefixes D A s (queryLaw D A s) := queryLaw_realizes D A s

example {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (A : StateEstimator R) (s : Fin N → Bool)
    (P Q : Measure (R × ProcessTape)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : RealizesQueryPrefixes D A s P) (hQ : RealizesQueryPrefixes D A s Q) : P = Q :=
  query_prefix_unique D A s P Q hP hQ

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) :
    ∃ D : CellDesign μ h δ,
      volume.map D.gap = μ ∧
      0 < cellDelta D.cap D.cell h ∧
      modulus μ h / 8 ≤ cellDelta D.cap D.cell h ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R)
        (P : (Fin D.count → Bool) → Measure (R × ProcessTape))
        [∀ s, IsProbabilityMeasure (P s)],
        (∀ s, RealizesQueryPrefixes (CellDesign.queryDesign μ h δ D) A s (P s)) →
        ∀ (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂P s) ≤ ENNReal.ofReal B) →
        (∀ s, P s {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) →
        (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B) :=
  variable_gap_observed_lower μ h hδ hd

example (d : Gap) (s : Bool) :
    (∫ b, binaryValue b ∂bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d)) =
      binaryMean d s := binary_mean d s

example (d : Gap) (s : Bool) : |binaryMean d s| = 2 * (d : ℝ) := binary_mean_magnitude d s

example (d : Gap) (s : Bool) :
    variance binaryValue (bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d)) =
      1 - 4 * (d : ℝ) ^ 2 := binary_variance d s

example (d : Gap) (hd : (d : ℝ) ≤ 1 / 4) (s : Bool) :
    3 / 4 ≤ variance binaryValue (bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d)) :=
  binary_variance_lower d hd s

example (d : Gap) (hd : (d : ℝ) ≤ 1 / 4) (s b : Bool) :
    |binaryValue b - binaryMean d s| ≤ 3 / 2 := binary_centered_bound d hd s b

example (d : Gap) (hd : (d : ℝ) ≤ 1 / 4) (s : Bool) {q : ℝ} (hq : 0 ≤ q) :
    (∫ b, (|binaryValue b - binaryMean d s| /
      Real.sqrt (variance binaryValue (bernoulliMeasure true false
        (ThresholdHC.ObservableSimulation.gapParameter s d)))) ^ q
      ∂bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d)) ≤ (3 : ℝ) ^ (q / 2) :=
  binary_standardized_moment d hd s hq

example (h : Gap) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : CellDesign uniformGaps h δ,
      (∀ u, (D.gap u : ℝ) ≤ 1 / 4) ∧ (∀ i, (D.cap i : ℝ) ≤ 1 / 4) :=
  uniform_design_exists h hδ

example {x : ℝ} (hx : 0 < x) :
    uniformGaps.real {d : Gap | (d : ℝ) ≤ x} = min 1 (4 * x) := uniformGaps_cdf hx

example {h : ℝ} (hh : 0 < h) (ha : h < 1 / 4) :
    modulus uniformGaps h = 4 * h * (1 + Real.log (1 / (4 * h))) := uniformGaps_modulus hh ha

example {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) :
    volume.real {u : unitInterval | 0 < ∫ b, binaryValue b ∂bernoulliMeasure true false
      (ThresholdHC.ObservableSimulation.gapParameter (s (D.cell u)) (D.gap u))} =
        stateTarget D.cell s := query_threshold_target D s

example :
    uniformGaps.map (fun d : Gap => normalizedGap d) =
      volume.withDensity (fun z => ENNReal.ofReal (normalizedDensity z)) := normalizedGap_density

example (z : ℝ) : 0 ≤ normalizedDensity z ∧ normalizedDensity z ≤ 2 := normalizedDensity_bounds z

example {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = uniformGaps) :
    volume.map (queryNormalizedMagnitude D s) =
      volume.withDensity (fun z => ENNReal.ofReal (normalizedDensity z)) := query_normalized_density D s hl

example {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (hd : ∀ u, (D.gap u : ℝ) ≤ 1 / 4) (u : unitInterval) {q : ℝ} (hq : 0 ≤ q) :
    (∫ b, (|binaryValue b -
      ∫ a, binaryValue a ∂bernoulliMeasure true false
        (ThresholdHC.ObservableSimulation.gapParameter (s (D.cell u)) (D.gap u))| /
        Real.sqrt (variance binaryValue
          (bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter (s (D.cell u)) (D.gap u))))) ^ q
      ∂bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter (s (D.cell u)) (D.gap u))) ≤
        (3 : ℝ) ^ (q / 2) := query_normalized_moment D s hd u hq

example {ε : ℝ} (hε : 0 < ε) (he : ε ≤ ThresholdHC.SmoothDensity.radiusCutoff 0) :
    ∃ h : Gap, (h : ℝ) ≤ 1 / 64 ∧
      (h : ℝ) = 64 * ε / Real.log (1 / ε) ∧ ε < modulus uniformGaps h / 32 :=
  choose_observed_scale hε he

example : 0 < lowerCoefficient := lowerCoefficient_pos

example {ε : ℝ} (hε : 0 < ε) (he : ε ≤ ThresholdHC.SmoothDensity.radiusCutoff 0) :
    ∃ (h : Gap) (D : CellDesign uniformGaps h (1 / 16)),
      (∀ u, (D.gap u : ℝ) ≤ 1 / 4) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R)
        (P : (Fin D.count → Bool) → Measure (R × ProcessTape))
        [∀ s, IsProbabilityMeasure (P s)],
        (∀ s, RealizesQueryPrefixes (CellDesign.queryDesign uniformGaps h (1 / 16) D) A s (P s)) →
        ∀ (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂P s) ≤ ENNReal.ofReal B) →
        (∀ s, P s {z | ε < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal (1 / 16)) →
        lowerCoefficient * (Real.log (1 / ε)) ^ 2 / ε ^ 2 ≤ B) :=
  uniform_confidence_lower hε he

example {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (u : unitInterval) :
    |∫ b, binaryValue b ∂bernoulliMeasure true false
      (ThresholdHC.ObservableSimulation.gapParameter (s (D.cell u)) (D.gap u))| / 2 =
        (D.gap u : ℝ) := query_gap_magnitude D s u

example {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (θ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hr : squaredRisk P f θ ≤ ENNReal.ofReal (ε ^ 2)) :
    P {z | 4 * ε < |f z - θ|} ≤ ENNReal.ofReal (1 / 16) := mse_fixed_confidence P f hf θ hε hr

example {ε : ℝ} (hε : 0 < ε)
    (he : ε ≤ min (ThresholdHC.SmoothDensity.radiusCutoff 0 / 4) (1 / 16)) :
    ∃ (h : Gap) (D : CellDesign uniformGaps h (1 / 16)),
      (∀ u, (D.gap u : ℝ) ≤ 1 / 4) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R)
        (P : (Fin D.count → Bool) → Measure (R × ProcessTape))
        [∀ s, IsProbabilityMeasure (P s)],
        (∀ s, RealizesQueryPrefixes (CellDesign.queryDesign uniformGaps h (1 / 16) D) A s (P s)) →
        ∀ (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂P s) ≤ ENNReal.ofReal B) →
        (∀ s, squaredRisk (P s) A.output (stateTarget D.cell s) ≤ ENNReal.ofReal (ε ^ 2)) →
        (lowerCoefficient / 64) * (Real.log (1 / ε)) ^ 2 / ε ^ 2 ≤ B) :=
  uniform_rms_lower hε he
#print axioms ThresholdHC.ContinuousObserved.binary_centered_bound
#print axioms ThresholdHC.ContinuousObserved.binary_mean
#print axioms ThresholdHC.ContinuousObserved.binary_mean_magnitude
#print axioms ThresholdHC.ContinuousObserved.binary_mean_positive
#print axioms ThresholdHC.ContinuousObserved.binary_standardized_bound
#print axioms ThresholdHC.ContinuousObserved.binary_standardized_moment
#print axioms ThresholdHC.ContinuousObserved.binary_variance
#print axioms ThresholdHC.ContinuousObserved.binary_variance_lower
#print axioms ThresholdHC.ContinuousObserved.capGap_clipped_bound
#print axioms ThresholdHC.ContinuousObserved.capGap_law
#print axioms ThresholdHC.ContinuousObserved.capGap_le
#print axioms ThresholdHC.ContinuousObserved.capGap_le_self
#print axioms ThresholdHC.ContinuousObserved.capGap_of_ge
#print axioms ThresholdHC.ContinuousObserved.capGap_of_le
#print axioms ThresholdHC.ContinuousObserved.cappedDesign
#print axioms ThresholdHC.ContinuousObserved.capped_delta_ge
#print axioms ThresholdHC.ContinuousObserved.choose_observed_scale
#print axioms ThresholdHC.ContinuousObserved.clippedGap_antitone
#print axioms ThresholdHC.ContinuousObserved.decodePrefix_cons_none
#print axioms ThresholdHC.ContinuousObserved.decodePrefix_cons_some
#print axioms ThresholdHC.ContinuousObserved.decodePrefix_none
#print axioms ThresholdHC.ContinuousObserved.decodePrefix_processPrefix
#print axioms ThresholdHC.ContinuousObserved.decodeTape_history
#print axioms ThresholdHC.ContinuousObserved.decodeTape_isSome
#print axioms ThresholdHC.ContinuousObserved.decodeTape_work
#print axioms ThresholdHC.ContinuousObserved.decode_append
#print axioms ThresholdHC.ContinuousObserved.decode_append_singleton
#print axioms ThresholdHC.ContinuousObserved.decode_length
#print axioms ThresholdHC.ContinuousObserved.decoded_population_prefix
#print axioms ThresholdHC.ContinuousObserved.fresh_observation_preserving
#print axioms ThresholdHC.ContinuousObserved.fresh_pair_preserving
#print axioms ThresholdHC.ContinuousObserved.hasDerivAt_inverseNormalizedGap
#print axioms ThresholdHC.ContinuousObserved.inverseNormalizedGap_endpoint
#print axioms ThresholdHC.ContinuousObserved.inverseNormalizedGap_mem_interval
#print axioms ThresholdHC.ContinuousObserved.inverseNormalizedGap_strictMono
#print axioms ThresholdHC.ContinuousObserved.inverseNormalizedGap_zero
#print axioms ThresholdHC.ContinuousObserved.inverseSlope_le
#print axioms ThresholdHC.ContinuousObserved.inverseSlope_pos
#print axioms ThresholdHC.ContinuousObserved.inverse_normalized_gap
#print axioms ThresholdHC.ContinuousObserved.lowerCoefficient_pos
#print axioms ThresholdHC.ContinuousObserved.measurable_capGap
#print axioms ThresholdHC.ContinuousObserved.measurable_decode
#print axioms ThresholdHC.ContinuousObserved.measurable_decodeTape
#print axioms ThresholdHC.ContinuousObserved.measurable_decoded
#print axioms ThresholdHC.ContinuousObserved.measurable_inverseSlope
#print axioms ThresholdHC.ContinuousObserved.measurable_noiseRate
#print axioms ThresholdHC.ContinuousObserved.measurable_noisyWord
#print axioms ThresholdHC.ContinuousObserved.measurable_normalizedDensity
#print axioms ThresholdHC.ContinuousObserved.measurable_normalizedGap
#print axioms ThresholdHC.ContinuousObserved.measurable_perturb
#print axioms ThresholdHC.ContinuousObserved.measurable_uniformTail
#print axioms ThresholdHC.ContinuousObserved.mse_fixed_confidence
#print axioms ThresholdHC.ContinuousObserved.noisyWord_decode
#print axioms ThresholdHC.ContinuousObserved.noisyWord_prefix_law
#print axioms ThresholdHC.ContinuousObserved.normalizedDensity_bounds
#print axioms ThresholdHC.ContinuousObserved.normalizedGap_density
#print axioms ThresholdHC.ContinuousObserved.normalizedGap_mem_support
#print axioms ThresholdHC.ContinuousObserved.normalized_inverse_gap
#print axioms ThresholdHC.ContinuousObserved.normalized_preimage
#print axioms ThresholdHC.ContinuousObserved.processHistory_succ
#print axioms ThresholdHC.ContinuousObserved.queryLaw_probability
#print axioms ThresholdHC.ContinuousObserved.queryLaw_realizes
#print axioms ThresholdHC.ContinuousObserved.queryNormalizedMagnitude_eq
#print axioms ThresholdHC.ContinuousObserved.query_confidence_lower
#print axioms ThresholdHC.ContinuousObserved.query_gap_magnitude
#print axioms ThresholdHC.ContinuousObserved.query_normalized_density
#print axioms ThresholdHC.ContinuousObserved.query_normalized_moment
#print axioms ThresholdHC.ContinuousObserved.query_prefix_unique
#print axioms ThresholdHC.ContinuousObserved.query_threshold_target
#print axioms ThresholdHC.ContinuousObserved.rawPolicy_shift
#print axioms ThresholdHC.ContinuousObserved.reduction_error
#print axioms ThresholdHC.ContinuousObserved.reduction_work
#print axioms ThresholdHC.ContinuousObserved.simulated_confidence_lower
#print axioms ThresholdHC.ContinuousObserved.stepNoise_shift
#print axioms ThresholdHC.ContinuousObserved.uniformGaps_cdf
#print axioms ThresholdHC.ContinuousObserved.uniformGaps_modulus
#print axioms ThresholdHC.ContinuousObserved.uniformGaps_probability
#print axioms ThresholdHC.ContinuousObserved.uniformGaps_real_law
#print axioms ThresholdHC.ContinuousObserved.uniformGaps_support
#print axioms ThresholdHC.ContinuousObserved.uniformTail_map
#print axioms ThresholdHC.ContinuousObserved.uniform_confidence_lower
#print axioms ThresholdHC.ContinuousObserved.uniform_design_exists
#print axioms ThresholdHC.ContinuousObserved.uniform_garbling_law
#print axioms ThresholdHC.ContinuousObserved.uniform_head_tail_independent
#print axioms ThresholdHC.ContinuousObserved.uniform_head_tail_preserving
#print axioms ThresholdHC.ContinuousObserved.uniform_rms_lower
#print axioms ThresholdHC.ContinuousObserved.variable_gap_observed_lower
