import ThresholdHC.BlindUpper.CallConsumes

/-! A generic observable controller for a finite plan of positive finite calls.
Its state stores only labels and observed words. Real-valued call outputs are
computed from those words after the controller halts. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

structure FiniteCall where
  cost : (ℕ → Bool) → ℕ
  value : (ℕ → Bool) → ℝ
  measurable_cost : Measurable cost
  measurable_value : Measurable value
  positive : ∀ ω, 0 < cost ω
  prefix_ext : ∀ ω ω', tapePrefix (cost ω) ω = tapePrefix (cost ω) ω' →
    cost ω' = cost ω ∧ value ω' = value ω

def observedDone (A : FiniteCall) (xs : List Bool) : Bool :=
  decide (A.cost (completeList xs) ≤ xs.length)

theorem observedDone_word (A : FiniteCall) (ω : ℕ → Bool) (n : ℕ) :
    observedDone A (tapeWord n ω) = decide (A.cost ω ≤ n) := by
  simp only [observedDone, tapeWord_length]
  congr 1
  exact propext (finiteCall_ready_iff (fun z : Unit × (ℕ → Bool) => A.cost z.2)
    (fun _ ω ω' h => (A.prefix_ext ω ω' h).1) () ω n)

theorem observedValue_word (A : FiniteCall) (ω : ℕ → Bool) :
    A.value (completeList (tapeWord (A.cost ω) ω)) = A.value ω :=
  (A.prefix_ext ω _ (completeList_tapeWord_prefix _ _).symm).2

structure PlanState where
  pending : List ℕ
  word : List Bool
  done : List (ℕ × List Bool)
  deriving Countable, DecidableEq

instance planStateMeasurableSpace : MeasurableSpace PlanState := ⊤

def planLabel (s : PlanState) : Option ℕ := s.pending.head?

def planStep (A : ℕ → FiniteCall) (s : PlanState) (b : Bool) : PlanState :=
  match s.pending with
  | [] => s
  | j::js =>
    let xs := s.word++[b]
    if observedDone (A j) xs then ⟨js, [], s.done++[(j,xs)]⟩ else ⟨j::js, xs, s.done⟩

def planRun (A : ℕ → FiniteCall) (s : PlanState) (xs : List Bool) : PlanState :=
  xs.foldl (planStep A) s

theorem planRun_append (A : ℕ → FiniteCall) (s : PlanState) (xs ys : List Bool) :
    planRun A s (xs++ys) = planRun A (planRun A s xs) ys := List.foldl_append

theorem planRun_absorbs (A : ℕ → FiniteCall) (s : PlanState) (hs : planLabel s = none) (xs : List Bool) :
    planRun A s xs = s := by
  have hp : s.pending = [] := List.head?_eq_none_iff.mp hs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change planRun A (planStep A s b) xs = s
    simpa [planStep, hp] using ih

theorem planRun_call_partial (A : ℕ → FiniteCall) (j : ℕ) (js : List ℕ)
    (done : List (ℕ × List Bool)) (ω : ℕ → Bool) (n : ℕ) (hn : n < (A j).cost ω) :
    planRun A ⟨j::js, [], done⟩ (tapeWord n ω) = ⟨j::js, tapeWord n ω, done⟩ := by
  induction n with
  | zero => simp [planRun, tapeWord]
  | succ n ih =>
    rw [tapeWord_succ, planRun_append, ih (by omega)]
    change planStep A ⟨j::js, tapeWord n ω, done⟩ (ω n) = _
    simp only [planStep]
    rw [← tapeWord_succ, observedDone_word]
    simp only [show ¬(A j).cost ω ≤ n+1 by omega, decide_false, Bool.false_eq_true, ite_false]

theorem planRun_call_complete (A : ℕ → FiniteCall) (j : ℕ) (js : List ℕ)
    (done : List (ℕ × List Bool)) (ω : ℕ → Bool) :
    planRun A ⟨j::js, [], done⟩ (tapeWord ((A j).cost ω) ω) =
      ⟨js, [], done++[(j,tapeWord ((A j).cost ω) ω)]⟩ := by
  let n := (A j).cost ω
  have hn : 0 < n := (A j).positive ω
  have he : n = (n-1)+1 := by omega
  change planRun A _ (tapeWord n ω) = _
  conv_lhs => rw [he, tapeWord_succ, planRun_append]
  rw [planRun_call_partial A j js done ω (n-1) (by omega)]
  change planStep A ⟨j::js, tapeWord (n-1) ω, done⟩ (ω (n-1)) = _
  simp only [planStep]
  rw [← tapeWord_succ, ← he, observedDone_word]
  simp only [show (A j).cost ω ≤ n from le_rfl, decide_true, ite_true]
  rfl

def planStateOutput (A : ℕ → FiniteCall) (s : PlanState) : ℝ :=
  (s.done.map (fun w => (A w.1).value (completeList w.2))).sum

def initialPlan (labels : List ℕ) : PlanState := ⟨labels, [], []⟩

def finitePlanPolicy {R : Type} (A : ℕ → FiniteCall) (plan : R → List ℕ)
    (r : R) (xs : List Bool) : Option ℕ := planLabel (planRun A (initialPlan (plan r)) xs)

def finitePlanHaltTime {R : Type} (A : ℕ → FiniteCall) (plan : R → List ℕ)
    (z : R × ProcessTape) : ℕ∞ :=
  firstSuccess (fun n => (finitePlanPolicy A plan z.1 (processHistory z.2 n)).isNone)

def finitePlanOutput {R : Type} (A : ℕ → FiniteCall) (plan : R → List ℕ)
    (z : R × ProcessTape) : ℝ :=
  planStateOutput A (planRun A (initialPlan (plan z.1))
    (processHistory z.2 (finitePlanHaltTime A plan z).toNat))

variable {R : Type} [Countable R] [MeasurableSpace R] [MeasurableSingletonClass R]

theorem measurable_finitePlanHaltTime (A : ℕ → FiniteCall) (plan : R → List ℕ) :
    Measurable (finitePlanHaltTime A plan) := by
  apply measurable_firstSuccess.comp
  apply Measurable.of_eval
  intro n
  have hp : Measurable (fun z : R × List Bool => (finitePlanPolicy A plan z.1 z.2).isNone) :=
    measurable_of_countable _
  exact hp.comp (measurable_fst.prodMk ((measurable_processHistory_fixed n).comp measurable_snd))

theorem measurable_finitePlanOutput (A : ℕ → FiniteCall) (plan : R → List ℕ) :
    Measurable (finitePlanOutput A plan) := by
  have ht := (measurable_of_countable ENat.toNat).comp (measurable_finitePlanHaltTime A plan)
  have hh : Measurable (fun z : ℕ × ProcessTape => processHistory z.2 z.1) :=
    measurable_from_prod_countable_right measurable_processHistory_fixed
  have hr : Measurable (fun z : R × List Bool => planStateOutput A (planRun A (initialPlan (plan z.1)) z.2)) :=
    measurable_of_countable _
  exact hr.comp (measurable_fst.prodMk (hh.comp (ht.prodMk measurable_snd)))

def finitePlanEstimator (ν : Measure R) [IsProbabilityMeasure ν]
    (A : ℕ → FiniteCall) (plan : R → List ℕ) : AdaptiveEstimator R where
  randomLaw := ν
  probability := inferInstance
  policy := finitePlanPolicy A plan
  policy_measurable := fun _xs _a => measurableSet_eq_fun (measurable_of_countable _) measurable_const
  output := finitePlanOutput A plan
  output_measurable := measurable_finitePlanOutput A plan

end ThresholdHC.EntropyTailExecution
