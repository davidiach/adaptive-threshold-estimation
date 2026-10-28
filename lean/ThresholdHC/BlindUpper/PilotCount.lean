import ThresholdHC.BlindUpper.MarkedCall
import ThresholdHC.BlindUpper.FirstSuccess
import ThresholdHC.BlindUpper.DoubleGeometric

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal

def markedTape {X : Type} (P : X → unitInterval) (z : ℕ → X × ℝ) : ℕ → Bool :=
  fun i => callMark P (z i)

theorem measurable_markedTape {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) : Measurable (markedTape P) :=
  Measurable.of_eval (fun i => (measurable_callMark P hP).comp (measurable_pi_apply i))

def markedSequenceLaw {X : Type} [MeasurableSpace X] (ν : Measure X) : Measure (ℕ → X × ℝ) :=
  Measure.infinitePi (fun _ : ℕ => ν.prod uniformUnitMeasure)

instance markedSequenceLaw_probability {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] : IsProbabilityMeasure (markedSequenceLaw ν) := by
  unfold markedSequenceLaw; infer_instance

def pilotFailures {X : Type} (P : X → unitInterval) (z : ℕ → X × ℝ) : ℕ :=
  (firstSuccess (markedTape P z)).toNat

theorem measurable_pilotFailures {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) : Measurable (pilotFailures P) :=
  (measurable_of_countable ENat.toNat).comp
    (measurable_firstSuccess.comp (measurable_markedTape P hP))

theorem pilot_terminates {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : meanParameter ν P hP ≠ 0) :
    ∀ᵐ z ∂markedSequenceLaw ν, firstSuccess (markedTape P z) ≠ ⊤ := by
  have h := firstSuccess_ae_finite (meanParameter ν P hP) hp
  rw [← callMarks_map ν P hP] at h
  apply (ae_map_iff (measurable_markedTape P hP).aemeasurable
    (measurable_firstSuccess (measurableSet_singleton (⊤ : ℕ∞))).compl).mp h

theorem pilotFailures_map {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : meanParameter ν P hP ≠ 0) :
    (markedSequenceLaw ν).map (pilotFailures P) = geometricMeasure (meanParameter ν P hP) := by
  have hm : Measurable (fun ω => (firstSuccess ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp measurable_firstSuccess
  change (markedSequenceLaw ν).map ((fun ω => (firstSuccess ω).toNat) ∘ markedTape P) = _
  rw [← Measure.map_map hm (measurable_markedTape P hP)]
  unfold markedSequenceLaw markedTape
  rw [callMarks_map ν P hP,firstSuccess_nat_map _ hp]

def twoPilotFailures {X : Type} (P : X → unitInterval)
    (z : (ℕ → X × ℝ) × (ℕ → X × ℝ)) : ℕ := pilotFailures P z.1+pilotFailures P z.2

theorem measurable_twoPilotFailures {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) : Measurable (twoPilotFailures P) :=
  ((measurable_pilotFailures P hP).comp measurable_fst).add
    ((measurable_pilotFailures P hP).comp measurable_snd)

theorem twoPilotFailures_map {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : meanParameter ν P hP ≠ 0) :
    ((markedSequenceLaw ν).prod (markedSequenceLaw ν)).map (twoPilotFailures P) =
      doubleFailuresLaw (meanParameter ν P hP) := by
  have hm := measurable_pilotFailures P hP
  change ((markedSequenceLaw ν).prod (markedSequenceLaw ν)).map
    ((fun z : ℕ × ℕ => z.1+z.2) ∘ Prod.map (pilotFailures P) (pilotFailures P)) = _
  rw [← Measure.map_map (measurable_of_countable _) (hm.prodMap hm),
    ← Measure.map_prod_map _ _ hm hm,pilotFailures_map ν P hP hp]
  rfl

theorem twoPilot_count_integrable {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : 0 < (meanParameter ν P hP : ℝ)) :
    Integrable (fun z => (twoPilotFailures P z : ℝ)+2)
      ((markedSequenceLaw ν).prod (markedSequenceLaw ν)) := by
  have hp' : meanParameter ν P hP ≠ 0 := by intro h; simp [h] at hp
  have hi := doubleFailures_count_integrable _ hp
  rw [← twoPilotFailures_map ν P hP hp'] at hi
  exact (integrable_map_measure
    (measurable_of_countable (fun n : ℕ => (n : ℝ)+2)).aestronglyMeasurable
    (measurable_twoPilotFailures P hP).aemeasurable).mp hi

theorem twoPilot_count_mean {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : 0 < (meanParameter ν P hP : ℝ)) :
    (∫ z, (twoPilotFailures P z : ℝ)+2 ∂(markedSequenceLaw ν).prod (markedSequenceLaw ν)) =
      2/(meanParameter ν P hP : ℝ) := by
  have hp' : meanParameter ν P hP ≠ 0 := by intro h; simp [h] at hp
  rw [← doubleFailures_count_mean _ hp,← twoPilotFailures_map ν P hP hp']
  exact (integral_map (measurable_twoPilotFailures P hP).aemeasurable
    (measurable_of_countable (fun n : ℕ => (n : ℝ)+2)).aestronglyMeasurable).symm

theorem twoPilot_inverse_mean {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : 0 < (meanParameter ν P hP : ℝ)) :
    (∫ z, ((twoPilotFailures P z : ℝ)+1)⁻¹ ∂(markedSequenceLaw ν).prod (markedSequenceLaw ν)) =
      (meanParameter ν P hP : ℝ) := by
  have hp' : meanParameter ν P hP ≠ 0 := by intro h; simp [h] at hp
  rw [← doubleFailures_inverse_mean _ hp,← twoPilotFailures_map ν P hP hp']
  exact (integral_map (measurable_twoPilotFailures P hP).aemeasurable
    (measurable_of_countable (fun n : ℕ => ((n : ℝ)+1)⁻¹)).aestronglyMeasurable).symm

end ThresholdHC.BlindUpper
