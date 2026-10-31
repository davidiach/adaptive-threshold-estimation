import ThresholdHC.EntropyTailExecution.CallMachine
import ThresholdHC.EntropyTailSampling.PositiveRace

/-! Adjacent calls use the same observed prefix; their charged cost is the
maximum of the two stopping times. Normalization changes only the output. -/

noncomputable section
open MeasureTheory
open scoped NNReal

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailSampling
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.EntropyTailAssembly
open ThresholdHC.CriticalEntropy

def scaleCall (a : ℝ) (A : FiniteCall) : FiniteCall where
  cost := A.cost
  value := fun ω => a*A.value ω
  measurable_cost := A.measurable_cost
  measurable_value := measurable_const.mul A.measurable_value
  positive := A.positive
  prefix_ext := by
    intro ω ω' h
    obtain ⟨hc,hv⟩ := A.prefix_ext ω ω' h
    exact ⟨hc, congrArg (a*·) hv⟩

def differenceCall (A B : FiniteCall) : FiniteCall where
  cost := fun ω => max (A.cost ω) (B.cost ω)
  value := fun ω => A.value ω-B.value ω
  measurable_cost := A.measurable_cost.max B.measurable_cost
  measurable_value := A.measurable_value.sub B.measurable_value
  positive := fun ω => lt_of_lt_of_le (A.positive ω) (le_max_left _ _)
  prefix_ext := by
    intro ω ω' h
    obtain ⟨ha,hv⟩ := A.prefix_ext ω ω' (prefix_eq_restrict h (le_max_left _ _))
    obtain ⟨hb,hw⟩ := B.prefix_ext ω ω' (prefix_eq_restrict h (le_max_right _ _))
    exact ⟨by rw [ha,hb], by rw [hv,hw]⟩

def incrementCall (A : ℕ → FiniteCall) : ℕ → FiniteCall
  | 0 => A 0
  | l+1 => differenceCall (A (l+1)) (A l)

theorem incrementCall_value (A : ℕ → FiniteCall) (l : ℕ) (ω : ℕ → Bool) :
    (incrementCall A l).value ω = ThresholdHC.Uniform713.increment (fun k => (A k).value ω) l := by
  cases l <;> rfl

theorem incrementCall_cost_le (A : ℕ → FiniteCall) (l : ℕ) (ω : ℕ → Bool) :
    ((incrementCall A l).cost ω:ℝ) ≤
      if l = 0 then ((A 0).cost ω:ℝ) else ((A l).cost ω:ℝ)+((A (l-1)).cost ω:ℝ) := by
  cases l with
  | zero => simp [incrementCall]
  | succ l =>
    simp only [incrementCall, differenceCall, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
    exact_mod_cast (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _) :
      max ((A (l+1)).cost ω) ((A l).cost ω) ≤ (A (l+1)).cost ω+(A l).cost ω)

def scheduledCall (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (l L : ℕ) : FiniteCall where
  cost := raceCost (negativeBankTest weights (levelEpsilon l))
    (positiveBankTest μ weights (ρ*levelEpsilon l)) L
  value := raceValue (negativeBankTest weights (levelEpsilon l))
    (positiveBankTest μ weights (ρ*levelEpsilon l)) L
  measurable_cost := measurable_raceCost _ _ _
  measurable_value := measurable_raceValue _ _ _
  positive := scheduled_raceCost_pos μ weights hw hρ hρ1 l L
  prefix_ext := race_prefix_ext _ _ _

end ThresholdHC.EntropyTailExecution
