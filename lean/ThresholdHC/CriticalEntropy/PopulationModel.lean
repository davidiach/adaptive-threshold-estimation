import ThresholdHC.CriticalEntropy.StoppedModel

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.CriticalEntropy

def uniformUnitMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance uniformUnitMeasure_probability : IsProbabilityMeasure uniformUnitMeasure where
  measure_univ := by simp [uniformUnitMeasure]

def uniformCoinFlip (p : unitInterval) (u : ℝ) : Bool :=
  if u < (p : ℝ) then true else false

theorem measurable_uniformCoinFlip :
    Measurable (fun z : unitInterval × ℝ => uniformCoinFlip z.1 z.2) := by
  unfold uniformCoinFlip
  exact Measurable.ite (measurableSet_lt measurable_snd (by fun_prop))
    measurable_const measurable_const

def uniformTapeMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => uniformUnitMeasure)

instance uniformTapeMeasure_probability : IsProbabilityMeasure uniformTapeMeasure := by
  unfold uniformTapeMeasure
  infer_instance

def uniformCoinTape (p : unitInterval) (u : ℕ → ℝ) : ℕ → Bool :=
  fun i => uniformCoinFlip p (u i)

theorem measurable_uniformCoinTape :
    Measurable (fun z : unitInterval × (ℕ → ℝ) => uniformCoinTape z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  exact measurable_uniformCoinFlip.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

def uniformProcedureState {R : Type} (z : unitInterval × (R × (ℕ → ℝ))) :
    R × (ℕ → Bool) := (z.2.1,uniformCoinTape z.1 z.2.2)

theorem measurable_uniformProcedureState {R : Type} [MeasurableSpace R] :
    Measurable (uniformProcedureState (R := R)) :=
  measurable_snd.fst.prodMk (measurable_uniformCoinTape.comp
    (measurable_fst.prodMk measurable_snd.snd))

/-- Extended raw second moment under the actual fixed-parameter tape law. -/
def conditionalSecondMoment {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((A.output z)^2) ∂ν.prod (Tier2.tapeMeasure p)

/-- The totalized Bochner integral; it represents an expectation only where
integrability has been established. Second moments and work retain infinity. -/
def conditionalMean {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ) : ℝ :=
  ∫ z, A.output z ∂ν.prod (Tier2.tapeMeasure p)

def mixtureParameter {D : Type} (p₀ p₁ q : D → unitInterval) (z : D × ℝ) : unitInterval :=
  if z.2 < (q z.1 : ℝ) then p₁ z.1 else p₀ z.1

theorem measurable_mixtureParameter {D : Type} [MeasurableSpace D]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) : Measurable (mixtureParameter p₀ p₁ q) := by
  unfold mixtureParameter
  exact Measurable.ite
    (measurableSet_lt measurable_snd ((measurable_subtype_coe.comp hq).comp measurable_fst))
    (h₁.comp measurable_fst) (h₀.comp measurable_fst)

def populationInput {D R : Type} (p₀ p₁ q : D → unitInterval)
    (z : D × (ℝ × (R × (ℕ → ℝ)))) : R × (ℕ → Bool) :=
  uniformProcedureState (mixtureParameter p₀ p₁ q (z.1,z.2.1),z.2.2)

theorem measurable_populationInput {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) : Measurable (populationInput (R := R) p₀ p₁ q) :=
  measurable_uniformProcedureState.comp
    (((measurable_mixtureParameter p₀ p₁ q h₀ h₁ hq).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

/-- The latent gap and sign selector generate a tape; the procedure receives
only its independent seed and that tape. -/
def populationMeasure {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) (ν : Measure R) : Measure (D × (ℝ × (R × (ℕ → ℝ)))) :=
  μ.prod (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure))

def populationSecondMoment {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((A.output (populationInput p₀ p₁ q z))^2) ∂populationMeasure μ ν

def populationExpectedWork {D R E : Type} [MeasurableSpace D] [MeasurableSpace R]
    [MeasurableSpace E] (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R E) : ℝ≥0∞ :=
  ∫⁻ z, stoppedProcedureWork A (populationInput p₀ p₁ q z) ∂populationMeasure μ ν

def populationMean {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R ℝ) : ℝ :=
  ∫ z, A.output (populationInput p₀ p₁ q z) ∂populationMeasure μ ν

end ThresholdHC.CriticalEntropy
