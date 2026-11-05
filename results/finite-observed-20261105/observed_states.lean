import ThresholdHC.ObservedState.Finite
import ThresholdHC.ObservedState.Garbling
import ThresholdHC.ObservedState.Rounding
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set ThresholdHC ThresholdHC.ObservedState
open ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.Tier6
open scoped ENNReal

example {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) :
    (∫ s, target w s ∂signLaw q) = ∑ i, w i * (q i : ℝ) := target_mean q w

example {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) :
    variance (target w) (signLaw q) = ∑ i, (w i) ^ 2 * (q i : ℝ) * (1 - (q i : ℝ)) :=
  target_variance q w

example {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) {r : ℝ} (hr : 0 < r) :
    (signLaw q) {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      ENNReal.ofReal ((∑ i, (w i) ^ 2) / (4 * r ^ 2)) := target_concentration q w hr

example (b d : Gap) (hd : (d : ℝ) ≤ b) (s : Bool) :
    ((bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s b)).prod
      (bernoulliMeasure true false (noiseRate b d hd))).map (fun z => Bool.xor z.1 z.2) =
        bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d) :=
  garbling_law b d hd s

example {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R)
    (d : Fin m → Gap) (q : Fin m → unitInterval) : IsProbabilityMeasure (bayesLaw A d q) :=
  bayesLaw_probability A d q

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (q : Fin m → unitInterval) (B : ℝ)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B) :
    (∫⁻ z, ThresholdHC.Tier3.totalProcessWork z.2 ∂bayesLaw A d q) ≤ ENNReal.ofReal B :=
  bayes_work_le A d q B hw

example (h : Gap) :
    ∃ T : Gap → Gap, Measurable T ∧ (Set.range T).Finite ∧
      (∀ d : Gap, d ≤ T d) ∧
      (∀ d : Gap, clippedGap h d ≤ 2 * clippedGap h (T d)) :=
  finite_upward_rounding h

example (μ : Measure Gap) (T : Gap → Gap) (hm : Measurable T)
    (hup : ∀ d, d ≤ T d) (x : ℝ) :
    (μ.map T) {d : Gap | (d : ℝ) ≤ x} ≤ μ {d : Gap | (d : ℝ) ≤ x} :=
  rounded_cdf_le μ T hm hup x

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) (T : Gap → Gap) (hm : Measurable T)
    (hb : ∀ d, clippedGap h d ≤ 2 * clippedGap h (T d)) :
    modulus μ h / 2 ≤ modulus (μ.map T) h := rounded_modulus_lower μ h T hm hb

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Tier6.Gap) (q : Fin m → unitInterval) :
    RealizesPrefixes A.randomLaw (bayesLaw A d q) Prod.fst Prod.snd A.policy
      (fun i => d i) (fun i => q i) :=
  bayes_realizes A d q

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h : ℝ} (hh : 0 < h) (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B) :
    klDiv (bayesLaw A d qp) (bayesLaw A d qm) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) :=
  bayes_information_bound A d η qp qm hp hm hh hη hd hw

example {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 2)
    (hP : 1 - e ≤ P.real E) (hQ : Q.real E ≤ e) :
    ENNReal.ofReal (klB (1 - e) e) ≤ klDiv P Q :=
  event_information_lower P Q E hE he he1 hP hQ

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (w η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h Δ δ : ℝ} (hB : 0 ≤ B) (hh : 0 < h) (hΔ : 0 < Δ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hsep : (∑ i, w i * (qp i : ℝ)) - (∑ i, w i * (qm i : ℝ)) = Δ)
    (hweights : (∑ i, (w i) ^ 2) ≤ δ * Δ ^ 2 / 16)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B)
    (hc : ThresholdHC.ObservedState.UniformConfidence A d w (Δ / 4) δ) :
    (225 / (128 * h ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B :=
  finite_confidence_lower A d w η qp qm hp hm hB hh hΔ hδ hδ1 hη hd hsep hweights hw hc

example {I : Type} [Fintype I] (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1)
    {M : ℕ} (hM : 0 < M) :
    (∑ i : I × Fin M, (replicatedWeight w M i) ^ 2) ≤ 1 / M :=
  replicated_square_le w hw hs hM

example {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ 1 / (M : ℝ) ≤ δ * Δ ^ 2 / 16 :=
  replication_count hΔ hδ

example (μ : Measure Gap) [IsProbabilityMeasure μ] (M : ℕ) [NeZero M] :
    ∃ f : unitInterval → Gap × Fin M, Measurable f ∧
      volume.map f = μ.prod (repetitionLaw M) := outer_source μ M

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (CellDesign μ h δ) := cell_design_exists μ h hδ

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) (δ : ℝ) (D : CellDesign μ h δ) :
    modulus μ h / 8 ≤ cellDelta D.cap D.cell h := design_separation μ h δ D

example {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (s : Fin N → Bool) (u : unitInterval) :
    (∫ b : Bool, (if b then (1 : ℝ) else -1)
      ∂bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter (s (cell u)) (cap (cell u)))) =
        conditionalMean cap cell s u := conditionalMean_exact cap cell s u

example {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (s : Fin N → Bool) (u : unitInterval) :
    |conditionalMean cap cell s u| = 2 * (cap (cell u) : ℝ) := conditionalMean_magnitude cap cell s u

example {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N) (s : Fin N → Bool) :
    volume.real {u | 0 < conditionalMean cap cell s u} = stateTarget cell s := threshold_target cap cell s

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) :
    ∃ D : CellDesign μ h δ,
      0 < cellDelta D.cap D.cell h ∧
      modulus μ h / 8 ≤ cellDelta D.cap D.cell h ∧
      (∀ x : ℝ, volume {u : unitInterval | (D.cap (D.cell u) : ℝ) ≤ x} ≤
        μ {d : Gap | (d : ℝ) ≤ x}) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R) (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A D.cap D.cell D.cell_measurable s) ≤ ENNReal.ofReal B) →
        (∀ s, stateLaw A D.cap D.cell D.cell_measurable s
          {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) →
        (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B) :=
  finite_observed_state_lower μ h hδ hd
#print axioms ThresholdHC.ObservedState.bayesLaw_probability
#print axioms ThresholdHC.ObservedState.bayes_event_bound
#print axioms ThresholdHC.ObservedState.bayes_information_bound
#print axioms ThresholdHC.ObservedState.bayes_realizes
#print axioms ThresholdHC.ObservedState.bayes_work_le
#print axioms ThresholdHC.ObservedState.cellWeight_sum
#print axioms ThresholdHC.ObservedState.cell_design_exists
#print axioms ThresholdHC.ObservedState.cell_mass
#print axioms ThresholdHC.ObservedState.cell_moment
#print axioms ThresholdHC.ObservedState.conditionalMean_exact
#print axioms ThresholdHC.ObservedState.conditionalMean_magnitude
#print axioms ThresholdHC.ObservedState.conditional_mean_positive
#print axioms ThresholdHC.ObservedState.design_cdf
#print axioms ThresholdHC.ObservedState.design_confidence_lower
#print axioms ThresholdHC.ObservedState.design_delta_pos
#print axioms ThresholdHC.ObservedState.design_separation
#print axioms ThresholdHC.ObservedState.event_information_lower
#print axioms ThresholdHC.ObservedState.finite_cell_law
#print axioms ThresholdHC.ObservedState.finite_confidence_lower
#print axioms ThresholdHC.ObservedState.finite_observed_state_lower
#print axioms ThresholdHC.ObservedState.finite_range_labels
#print axioms ThresholdHC.ObservedState.finite_upward_rounding
#print axioms ThresholdHC.ObservedState.fixed_word_law
#print axioms ThresholdHC.ObservedState.garbled_parameter
#print axioms ThresholdHC.ObservedState.garbling_law
#print axioms ThresholdHC.ObservedState.labelWeight_nonneg
#print axioms ThresholdHC.ObservedState.labelWeight_sum
#print axioms ThresholdHC.ObservedState.label_moment
#print axioms ThresholdHC.ObservedState.measurable_observation
#print axioms ThresholdHC.ObservedState.measurable_pathProb_policy
#print axioms ThresholdHC.ObservedState.measurable_raiseGap
#print axioms ThresholdHC.ObservedState.modelLaw_probability
#print axioms ThresholdHC.ObservedState.model_prefix_integral
#print axioms ThresholdHC.ObservedState.onCells_policy
#print axioms ThresholdHC.ObservedState.outer_gap_law
#print axioms ThresholdHC.ObservedState.outer_source
#print axioms ThresholdHC.ObservedState.raiseGap_bounds
#print axioms ThresholdHC.ObservedState.raiseGap_clipped
#print axioms ThresholdHC.ObservedState.repetitionLaw_probability
#print axioms ThresholdHC.ObservedState.repetitionLaw_singleton
#print axioms ThresholdHC.ObservedState.replicated_moment
#print axioms ThresholdHC.ObservedState.replicated_square_le
#print axioms ThresholdHC.ObservedState.replicated_square_sum
#print axioms ThresholdHC.ObservedState.replicated_sum
#print axioms ThresholdHC.ObservedState.replication_count
#print axioms ThresholdHC.ObservedState.rounded_cdf_le
#print axioms ThresholdHC.ObservedState.rounded_modulus_lower
#print axioms ThresholdHC.ObservedState.signLaw_singleton
#print axioms ThresholdHC.ObservedState.signLaw_total
#print axioms ThresholdHC.ObservedState.small_weights_concentrate
#print axioms ThresholdHC.ObservedState.stateEstimator_probability
#print axioms ThresholdHC.ObservedState.stateTarget_eq
#print axioms ThresholdHC.ObservedState.target_concentration
#print axioms ThresholdHC.ObservedState.target_mean
#print axioms ThresholdHC.ObservedState.target_memLp
#print axioms ThresholdHC.ObservedState.target_variance
#print axioms ThresholdHC.ObservedState.target_variance_le
#print axioms ThresholdHC.ObservedState.threshold_target
