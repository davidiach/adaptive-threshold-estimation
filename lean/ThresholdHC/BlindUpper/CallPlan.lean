import ThresholdHC.BlindUpper.CallConsumes

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open scoped ENNReal
/-- A finite plan records only legal successive calls on specified labels. -/
inductive CallPlan (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) :
    BatchControl → List ℕ → BatchControl → Prop
  | nil (c : BatchControl) : CallPlan L r s c [] c
  | cons {c c' : BatchControl} {j : ℕ} {js : List ℕ}
      (action : controlLabel c = some j)
      (rest : CallPlan L r s (controlAdvance L r c (batchCallWord L r s j)) js c') :
      CallPlan L r s c (j::js) c'

def callWords (L : ℕ) (r : BatchSeed) (s : ℕ → ℕ → Bool) (js : List ℕ) : List Bool :=
  js.flatMap (batchCallWord L r s)

theorem CallPlan.state_eq {L : ℕ} {r : BatchSeed} {s : ℕ → ℕ → Bool}
    {c c' : BatchControl} {js : List ℕ} (h : CallPlan L r s c js c') :
    batchRun L r (c,[]) (callWords L r s js) = (c',[]) := by
  induction h with
  | nil => rfl
  | @cons c c' j js ha rest ih =>
    change batchRun L r (c,[]) (batchCallWord L r s j++callWords L r s js) = _
    rw [batchRun_append]
    change batchRun L r (batchRun L r (c,[])
      (tapeWord (paddedCutoffCost L ((r j).1,s j)) (s j))) _ = _
    rw [batchRun_call_complete L r c j ha]
    exact ih

theorem CallPlan.append {L : ℕ} {r : BatchSeed} {s : ℕ → ℕ → Bool}
    {c mid last : BatchControl} {xs ys : List ℕ}
    (h : CallPlan L r s c xs mid) (h' : CallPlan L r s mid ys last) :
    CallPlan L r s c (xs++ys) last := by
  induction h with
  | nil => exact h'
  | cons ha rest ih => exact .cons ha (ih h')

theorem CallPlan.consumes {L : ℕ} {r : BatchSeed} {s : ℕ → ℕ → Bool}
    {c c' : BatchControl} {js : List ℕ} (h : CallPlan L r s c js c')
    (hn : js.Nodup) (t : ℕ → ℕ → Bool) (hfresh : ∀ j ∈ js, t j = s j) :
    ∃ t', BatchConsumes L r (c,[]) t (callWords L r s js) (c',[]) t' := by
  induction h generalizing t with
  | nil c => exact ⟨t,.nil _ _⟩
  | @cons c c' j js ha rest ih =>
    have hnodup := List.nodup_cons.mp hn
    have hj : t j = s j := hfresh j (by simp)
    let u := Function.update t j (tapeDrop (paddedCutoffCost L ((r j).1,s j)) (s j))
    have hu : ∀ k ∈ js, u k = s k := by
      intro k hk
      have hkj : k ≠ j := by intro he; subst k; exact hnodup.1 hk
      rw [show u k = t k from Function.update_of_ne hkj _ _]
      exact hfresh k (by simp [hk])
    obtain ⟨t',ht'⟩ := ih hnodup.2 u hu
    have hcall := consumes_call L r c t j ha
    have hw : batchCallWord L r t j = batchCallWord L r s j := by simp only [batchCallWord,hj]
    rw [hw,hj] at hcall
    exact ⟨t',hcall.append ht'⟩

theorem CallPlan.path_eq {L : ℕ} {r : BatchSeed} {s : ℕ → ℕ → Bool}
    {c c' : BatchControl} {js : List ℕ} (h : CallPlan L r s c js c')
    (hn : js.Nodup) (halt : controlLabel c' = none) :
    populationPath (statePolicy L r (c,[])) s = fun n => (callWords L r s js)[n]? := by
  obtain ⟨t,ht⟩ := h.consumes hn s (fun _ _ => rfl)
  exact ht.path_eq halt

end ThresholdHC.BlindUpper
