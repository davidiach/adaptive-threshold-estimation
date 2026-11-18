import SharpTapeLaw
import SharpArrayLaw

/-! Lift a verified single-coin tape coupling to a measurable estimator of
the original population experiment, preserving its uniform work budget. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 Tier5 Tier6 CriticalEntropy ContinuousObserved ObservableSimulation
open scoped ENNReal

abbrev NoiseCoin := Gap × (ℕ → ℝ)
abbrev SourceSeed (R : Type) := R × (ℕ → NoiseCoin)

def response {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap) (r : SourceSeed R) :=
  localResponse (A.policy r.1) (fun i => coinDecoder (r.2 i).1 g 0 0 (r.2 i).2)

theorem measurable_response {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap)
    (xs : List Bool) (b : Bool) : Measurable (fun r : SourceSeed R => response A g r xs b) :=
  measurable_localResponse (fun r : SourceSeed R => A.policy r.1)
    (fun ys o => measurable_fst (A.policy_measurable ys o)) _
    (fun i ys y => (measurable_coinDecoder g 0 0 ys y).comp ((measurable_pi_apply i).comp measurable_snd)) xs b

def targetObservation {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap)
    (z : SourceSeed R × ProcessTape) : R × ProcessTape :=
  (z.1.1,decodeTape (response A g z.1) z.2)

theorem measurable_targetObservation {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap) :
    Measurable (targetObservation A g) :=
  (measurable_fst.comp measurable_fst).prodMk (measurable_decodeTape _ (measurable_response A g))

def sourceEstimator {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) : AdaptiveEstimator (SourceSeed R) where
  randomLaw := A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => μ.prod uniformTapeMeasure))
  probability := inferInstance
  policy := fun r xs => A.policy r.1 (decode (response A g r) xs)
  policy_measurable := by
    intro xs o
    have ma : Measurable (fun z : R × List Bool => A.policy z.1 z.2) :=
      measurable_from_prod_countable_left (fun ys => measurable_to_countable' (A.policy_measurable ys))
    have md := measurable_decode (response A g) (measurable_response A g) xs
    exact (ma.comp (measurable_fst.prodMk md)) (measurableSet_singleton o)
  output := fun z => (A.output (targetObservation A g z)-(1-modulus μ g.val)/2)/modulus μ g.val
  output_measurable := ((A.output_measurable.comp (measurable_targetObservation A g)).sub measurable_const).div_const _

/-- Exact identity of all measurable nonnegative observable tests. -/
theorem transferred_observation {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) (q q' : SignLaw)
    (tapes : ((μ.prod uniformTapeMeasure).prod (originalPopulationTapeLaw (Measure.dirac g) q)).map
       (fun z => virtualTape z.1.1 g 0 0 z.1.2 z.2) = originalPopulationTapeLaw μ q')
    (F : R × ProcessTape → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (targetObservation A g (z.1.1,z.2)) ∂experimentLaw (Measure.dirac g) (sourceEstimator μ g A) q) =
      ∫⁻ z, F (z.1.1,z.2) ∂experimentLaw μ A q' := by
  let S := sourceEstimator μ g A
  let N := μ.prod uniformTapeMeasure
  let U := originalPopulationTapeLaw (Measure.dirac g) q
  let T := originalPopulationTapeLaw μ q'
  let V := fun z : NoiseCoin × (ℕ → Bool) => virtualTape z.1.1 g 0 0 z.1.2 z.2
  let φ := fun z : (ℕ → NoiseCoin) × (ℕ → ℕ → Bool) => fun i => V (z.1 i,z.2 i)
  have mv : Measurable V := measurable_virtualTape_joint g 0 0
  have mp : Measurable φ := Measurable.of_eval (fun i => mv.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have push : MeasurePreserving φ
      ((Measure.infinitePi (fun _ : ℕ => N)).prod (Measure.infinitePi (fun _ : ℕ => U)))
      (Measure.infinitePi (fun _ : ℕ => T)) :=
    ⟨mp,(transform_population N U V mv).trans (congrArg (fun ν => Measure.infinitePi (fun _ : ℕ => ν)) tapes)⟩
  have all := ((MeasurePreserving.id A.randomLaw).prod push).comp
    (measurePreserving_prodAssoc A.randomLaw (Measure.infinitePi (fun _ : ℕ => N)) (Measure.infinitePi (fun _ : ℕ => U)))
  let G := fun z : R × (ℕ → ℕ → Bool) => F (z.1,populationPath (A.policy z.1) z.2)
  have mG : Measurable G := hF.comp (measurable_fst.prodMk (measurable_seeded_populationPath A.policy
    (fun ys => measurable_to_countable' (A.policy_measurable ys))))
  rw [original_observable_lintegral (Measure.dirac g) S q (fun z => F (targetObservation A g z))
        (hF.comp (measurable_targetObservation A g)), original_observable_lintegral μ A q' F hF]
  apply Eq.trans _ (all.lintegral_comp mG)
  apply lintegral_congr
  intro z
  apply congrArg F
  change (z.1.1,_) = (z.1.1,_)
  congr 1
  exact causal_population_path (A.policy z.1.1) (fun i => coinDecoder (z.1.2 i).1 g 0 0 (z.1.2 i).2) z.2

end ThresholdHC.SharpRMS
