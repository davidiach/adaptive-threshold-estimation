import ThresholdHC.EntropyTailExecution.CallMachine

/-! Every planned call reveals exactly its own stopped prefix. Distinct
labels guarantee fresh population tapes and every consumed bit is charged. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

def statePolicy (A : ℕ → FiniteCall) (s : PlanState) (xs : List Bool) : Option ℕ :=
  planLabel (planRun A s xs)

inductive PlanConsumes (A : ℕ → FiniteCall) :
    PlanState → (ℕ → ℕ → Bool) → List Bool → PlanState → (ℕ → ℕ → Bool) → Prop
  | nil (st : PlanState) (s : ℕ → ℕ → Bool) : PlanConsumes A st s [] st s
  | cons {st st' : PlanState} {s s' : ℕ → ℕ → Bool} {j : ℕ} {b : Bool} {xs : List Bool}
      (action : planLabel st = some j) (bit : s j 0 = b)
      (rest : PlanConsumes A (planStep A st b) (Function.update s j (tapeDrop 1 (s j))) xs st' s') :
      PlanConsumes A st s (b::xs) st' s'

theorem PlanConsumes.state_eq {A : ℕ → FiniteCall} {st st' : PlanState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : PlanConsumes A st s xs st' s') :
    planRun A st xs = st' := by
  induction h with
  | nil => rfl
  | cons ha hb rest ih => exact ih

theorem PlanConsumes.append {A : ℕ → FiniteCall} {st mid last : PlanState}
    {s t u : ℕ → ℕ → Bool} {xs ys : List Bool}
    (h : PlanConsumes A st s xs mid t) (h' : PlanConsumes A mid t ys last u) :
    PlanConsumes A st s (xs++ys) last u := by
  induction h with
  | nil => exact h'
  | cons ha hb rest ih => exact .cons ha hb (ih h')

theorem PlanConsumes.path_eq {A : ℕ → FiniteCall} {st st' : PlanState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : PlanConsumes A st s xs st' s')
    (ht : planLabel st' = none) : populationPath (statePolicy A st) s = fun n => xs[n]? := by
  induction h with
  | nil st s =>
    rw [populationPath_none _ _ ht]
    rfl
  | @cons st st' s s' j b xs ha hb rest ih =>
    funext n
    cases n with
    | zero => simp [populationPath_zero, statePolicy, planRun, ha, hb]
    | succ n =>
      rw [populationPath_succ _ _ j n ha, hb]
      change populationPath (statePolicy A (planStep A st b))
        (Function.update s j (tapeDrop 1 (s j))) n = _
      rw [ih ht]
      rfl

def callWord (A : ℕ → FiniteCall) (s : ℕ → ℕ → Bool) (j : ℕ) : List Bool :=
  tapeWord ((A j).cost (s j)) (s j)

def planWord (A : ℕ → FiniteCall) (s : ℕ → ℕ → Bool) (labels : List ℕ) : List Bool :=
  labels.flatMap (callWord A s)

def planRecords (A : ℕ → FiniteCall) (s : ℕ → ℕ → Bool) (labels : List ℕ) : List (ℕ × List Bool) :=
  labels.map (fun j => (j,callWord A s j))

theorem consumes_call_prefix (A : ℕ → FiniteCall) (s : ℕ → ℕ → Bool)
    (j : ℕ) (js : List ℕ) (done : List (ℕ × List Bool)) (n : ℕ) (hn : n ≤ (A j).cost (s j)) :
    PlanConsumes A ⟨j::js, [], done⟩ s (tapeWord n (s j))
      (planRun A ⟨j::js, [], done⟩ (tapeWord n (s j)))
      (Function.update s j (tapeDrop n (s j))) := by
  induction n with
  | zero =>
    have hd : tapeDrop 0 (s j) = s j := by funext k; simp [tapeDrop]
    simp only [hd, Function.update_eq_self, tapeWord, List.ofFn_zero, planRun, List.foldl_nil]
    exact .nil _ _
  | succ n ih =>
    have hprev := ih (by omega)
    have hs := planRun_call_partial A j js done (s j) n (by omega)
    rw [hs] at hprev
    have hsingle : PlanConsumes A ⟨j::js, tapeWord n (s j), done⟩
        (Function.update s j (tapeDrop n (s j))) [s j n]
        (planStep A ⟨j::js, tapeWord n (s j), done⟩ (s j n))
        (Function.update s j (tapeDrop (n+1) (s j))) := by
      rw [← updated_tape_advance]
      exact .cons rfl (by simp [tapeDrop]) (.nil _ _)
    have h := hprev.append hsingle
    rw [← tapeWord_succ] at h
    convert h using 1
    rw [tapeWord_succ, planRun_append, hs]
    rfl

theorem consumes_call (A : ℕ → FiniteCall) (s : ℕ → ℕ → Bool)
    (j : ℕ) (js : List ℕ) (done : List (ℕ × List Bool)) :
    PlanConsumes A ⟨j::js, [], done⟩ s (callWord A s j)
      ⟨js, [], done++[(j,callWord A s j)]⟩
      (Function.update s j (tapeDrop ((A j).cost (s j)) (s j))) := by
  have h := consumes_call_prefix A s j js done ((A j).cost (s j)) le_rfl
  rw [planRun_call_complete] at h
  exact h

theorem full_plan_consumes (A : ℕ → FiniteCall) (s : ℕ → ℕ → Bool) (labels : List ℕ)
    (hn : labels.Nodup) (done : List (ℕ × List Bool)) (t : ℕ → ℕ → Bool)
    (hfresh : ∀ j ∈ labels, t j = s j) :
    ∃ t', PlanConsumes A ⟨labels, [], done⟩ t (planWord A s labels)
      ⟨[], [], done++planRecords A s labels⟩ t' := by
  induction labels generalizing done t with
  | nil => exact ⟨t, by simpa [planWord, planRecords] using PlanConsumes.nil (A := A) ⟨[], [], done⟩ t⟩
  | cons j js ih =>
    have hnodup := List.nodup_cons.mp hn
    have hj : t j = s j := hfresh j (by simp)
    let u := Function.update t j (tapeDrop ((A j).cost (s j)) (s j))
    have hu : ∀ k ∈ js, u k = s k := by
      intro k hk
      have hkj : k ≠ j := by intro he; subst k; exact hnodup.1 hk
      rw [show u k = t k from Function.update_of_ne hkj _ _]
      exact hfresh k (by simp [hk])
    obtain ⟨t', ht'⟩ := ih hnodup.2 (done++[(j,callWord A s j)]) u hu
    have hcall := consumes_call A t j js done
    have hw : callWord A t j = callWord A s j := by simp only [callWord, hj]
    rw [hw, hj] at hcall
    refine ⟨t', ?_⟩
    simpa only [planWord, List.flatMap_cons, planRecords, List.map_cons, List.append_assoc, List.singleton_append]
      using hcall.append ht'

theorem finitePlan_path_eq (A : ℕ → FiniteCall) (s : ℕ → ℕ → Bool)
    (labels : List ℕ) (hn : labels.Nodup) :
    populationPath (statePolicy A (initialPlan labels)) s = fun n => (planWord A s labels)[n]? := by
  obtain ⟨t, ht⟩ := full_plan_consumes A s labels hn [] s (fun _ _ => rfl)
  exact ht.path_eq rfl

end ThresholdHC.EntropyTailExecution
