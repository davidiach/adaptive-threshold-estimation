import ThresholdHC.Observable713.Classifier
import ThresholdHC.BlindUpper.CallObservation
import ThresholdHC.Observable713.Specification
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! One geometric seed, one population coin, and the original 713 stopping rule. -/

noncomputable section
namespace ThresholdHC.Observable713
open MeasureTheory ThresholdHC.Uniform713 ThresholdHC.BlindUpper
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

def policy (l : ℕ) (xs : List Bool) : Option ℕ :=
  if callCost (l,completeList xs) ≤ xs.length then none else some 0

theorem measurable_policy : MeasurableCreationPolicy policy := by
  intro xs a
  exact Set.to_countable _ |>.measurableSet

/-- The stopped transcript is padded by `none`; decoding it supplies no new flips. -/
def decodedTape (x : ProcessTape) : ℕ → Bool := fun n => (x n).getD false

theorem measurable_decodedTape : Measurable decodedTape :=
  Measurable.of_eval (fun n =>
    (measurable_of_countable (fun b : Option Bool => b.getD false)).comp (measurable_pi_apply n))

def output (z : ℕ × ProcessTape) : ℝ := callValue (z.1,decodedTape z.2)

theorem measurable_output : Measurable output :=
  measurable_callValue.comp (measurable_fst.prodMk (measurable_decodedTape.comp measurable_snd))

/-- This estimator is fixed before both the gap law and the sign law. -/
def observableEstimator : AdaptiveEstimator ℕ where
  randomLaw := levelMeasure
  probability := levelMeasure_probability
  policy := policy
  policy_measurable := measurable_policy
  output := output
  output_measurable := measurable_output

theorem policy_word (l n : ℕ) (ω : ℕ → Bool) :
    policy l (tapeWord n ω) = if callCost (l,ω) ≤ n then none else some 0 := by
  simp only [policy,tapeWord_length,
    finiteCall_ready_iff callCost (fun r a b h => (call_prefix_ext r a b h).1)]

end ThresholdHC.Observable713
