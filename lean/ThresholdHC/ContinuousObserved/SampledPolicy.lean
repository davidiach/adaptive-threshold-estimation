import ThresholdHC.ContinuousObserved.QueryPrefix

noncomputable section
open MeasureTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.ObservedState

def outerSequenceLaw : Measure (ℕ → unitInterval) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

instance outerSequenceLaw_probability : IsProbabilityMeasure outerSequenceLaw := by
  unfold outerSequenceLaw
  infer_instance

/-- Each original coin label is assigned an independent uniform outer state.
The policy and output use the same observations as the original estimator. -/
def sampledStateEstimator {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) :
    StateEstimator (R × (ℕ → unitInterval)) where
  randomLaw := A.randomLaw.prod outerSequenceLaw
  probability := inferInstance
  continues := fun z xs => (A.policy z.1 xs).isSome
  continues_measurable := by
    intro xs
    have hp : Measurable (fun z : R × (ℕ → unitInterval) => A.policy z.1 xs) :=
      (measurable_to_countable' (fun i => A.policy_measurable xs i)).comp measurable_fst
    exact (measurable_of_countable (fun i : Option ℕ => i.isSome)).comp hp
  query := fun z xs => match A.policy z.1 xs with
    | none => 0
    | some i => z.2 i
  query_measurable := by
    intro xs
    let f (i : Option ℕ) (z : R × (ℕ → unitInterval)) : unitInterval :=
      match i with
      | none => 0
      | some j => z.2 j
    have hf (i : Option ℕ) : Measurable (f i) := by
      cases i with
      | none => exact measurable_const
      | some j => exact (measurable_pi_apply j).comp measurable_snd
    have hm : Measurable (fun z : Option ℕ × (R × (ℕ → unitInterval)) => f z.1 z.2) :=
      measurable_from_prod_countable_right hf
    have hp : Measurable (fun z : R × (ℕ → unitInterval) => A.policy z.1 xs) :=
      (measurable_to_countable' (fun i => A.policy_measurable xs i)).comp measurable_fst
    exact hm.comp (hp.prodMk measurable_id)
  output := fun z => A.output (z.1.1,z.2)
  output_measurable := A.output_measurable.comp (measurable_fst.fst.prodMk measurable_snd)

end ThresholdHC.ContinuousObserved
