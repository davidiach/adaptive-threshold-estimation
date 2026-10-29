import ThresholdHC.RareAboveTwo.CoupledModel
import ThresholdHC.Observable713.Execution

/-! The finite call is executed using coin zero and its observed flips only. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ThresholdHC.Uniform713 ThresholdHC.BlindUpper
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

def callCost (a ρ : ℝ) (z : ℕ × (ℕ → Bool)) : ℕ := coupledCost a ρ z.1 z.2
def callValue (a ρ : ℝ) (z : ℕ × (ℕ → Bool)) : ℝ := coupledValue a ρ z.1 z.2

theorem measurable_callCost (a ρ : ℝ) : Measurable (callCost a ρ) :=
  measurable_from_prod_countable_right (measurable_coupledCost a ρ)

theorem measurable_callValue (a ρ : ℝ) : Measurable (callValue a ρ) :=
  measurable_from_prod_countable_right (measurable_coupledValue a ρ)

theorem call_prefix_ext (a ρ : ℝ) (j : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (callCost a ρ (j,ω)) ω = Tier2.tapePrefix (callCost a ρ (j,ω)) ω') :
    callCost a ρ (j,ω') = callCost a ρ (j,ω) ∧ callValue a ρ (j,ω') = callValue a ρ (j,ω) :=
  coupled_prefix_ext a ρ j ω ω' h

def policy (a ρ : ℝ) (l : ℕ) (xs : List Bool) : Option ℕ :=
  if callCost a ρ (l,completeList xs) ≤ xs.length then none else some 0

theorem measurable_policy (a ρ : ℝ) : MeasurableCreationPolicy (policy a ρ) := by
  intro xs a
  exact Set.to_countable _ |>.measurableSet

def output (a ρ : ℝ) (z : ℕ × ProcessTape) : ℝ := callValue a ρ (z.1,Observable713.decodedTape z.2)

theorem measurable_output (a ρ : ℝ) : Measurable (output a ρ) :=
  (measurable_callValue a ρ).comp (measurable_fst.prodMk (Observable713.measurable_decodedTape.comp measurable_snd))

/-- This estimator is fixed before both the gap law and the sign law. -/
def observableEstimator (a ρ : ℝ) : AdaptiveEstimator ℕ where
  randomLaw := levelMeasure
  probability := levelMeasure_probability
  policy := policy a ρ
  policy_measurable := measurable_policy a ρ
  output := output a ρ
  output_measurable := measurable_output a ρ

theorem policy_word (a ρ : ℝ) (l n : ℕ) (ω : ℕ → Bool) :
    policy a ρ l (tapeWord n ω) = if callCost a ρ (l,ω) ≤ n then none else some 0 := by
  simp only [policy,tapeWord_length,
    finiteCall_ready_iff (callCost a ρ) (fun r x y h => (call_prefix_ext a ρ r x y h).1)]

end ThresholdHC.RareAboveTwo
