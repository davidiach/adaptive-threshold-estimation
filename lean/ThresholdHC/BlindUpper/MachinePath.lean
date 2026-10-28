import ThresholdHC.BlindUpper.ControllerExecution

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation

def statePolicy (L : ℕ) (r : BatchSeed) (s : BatchMachineState) (xs : List Bool) : Option ℕ :=
  controlLabel (batchRun L r s xs).1

theorem populationPath_zero (pol : List Bool → Option ℕ) (s : ℕ → ℕ → Bool) :
    populationPath pol s 0 = (pol []).map (fun j => s j 0) := by
  cases h : pol [] <;> simp [populationPath,populationSimulation,h]

theorem populationPath_succ (pol : List Bool → Option ℕ) (s : ℕ → ℕ → Bool) (j n : ℕ)
    (hj : pol [] = some j) :
    populationPath pol s (n+1) = populationPath (fun xs => pol (s j 0::xs))
      (Function.update s j (tapeDrop 1 (s j))) n := by
  simp only [populationPath]
  rw [populationSimulation,hj]
  rfl

theorem populationPath_none (pol : List Bool → Option ℕ) (s : ℕ → ℕ → Bool)
    (h : pol [] = none) : populationPath pol s = fun _ => none := by
  funext n
  simp [populationPath,populationSimulation,h]

/-- Exact finite execution with every input bit charged to its chosen tape. -/
inductive BatchConsumes (L : ℕ) (r : BatchSeed) :
    BatchMachineState → (ℕ → ℕ → Bool) → List Bool → BatchMachineState → (ℕ → ℕ → Bool) → Prop
  | nil (st : BatchMachineState) (s : ℕ → ℕ → Bool) : BatchConsumes L r st s [] st s
  | cons {st st' : BatchMachineState} {s s' : ℕ → ℕ → Bool} {j : ℕ} {b : Bool} {xs : List Bool}
      (action : controlLabel st.1 = some j) (bit : s j 0 = b)
      (rest : BatchConsumes L r (batchStep L r st b)
        (Function.update s j (tapeDrop 1 (s j))) xs st' s') :
      BatchConsumes L r st s (b::xs) st' s'

theorem BatchConsumes.state_eq {L : ℕ} {r : BatchSeed} {st st' : BatchMachineState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : BatchConsumes L r st s xs st' s') :
    batchRun L r st xs = st' := by
  induction h with
  | nil => rfl
  | cons ha hb rest ih => exact ih

theorem BatchConsumes.append {L : ℕ} {r : BatchSeed} {st mid last : BatchMachineState}
    {s t u : ℕ → ℕ → Bool} {xs ys : List Bool}
    (h : BatchConsumes L r st s xs mid t) (h' : BatchConsumes L r mid t ys last u) :
    BatchConsumes L r st s (xs++ys) last u := by
  induction h with
  | nil => exact h'
  | cons ha hb rest ih => exact .cons ha hb (ih h')

/-- A terminal finite execution determines the whole padded population path. -/
theorem BatchConsumes.path_eq {L : ℕ} {r : BatchSeed} {st st' : BatchMachineState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : BatchConsumes L r st s xs st' s')
    (ht : controlLabel st'.1 = none) :
    populationPath (statePolicy L r st) s = fun n => xs[n]? := by
  induction h with
  | nil st s =>
    rw [populationPath_none _ _ ht]
    rfl
  | @cons st st' s s' j b xs ha hb rest ih =>
    funext n
    cases n with
    | zero => simp [populationPath_zero,statePolicy,batchRun,ha,hb]
    | succ n =>
      rw [populationPath_succ _ _ j n ha,hb]
      change populationPath (statePolicy L r (batchStep L r st b))
        (Function.update s j (tapeDrop 1 (s j))) n = _
      rw [ih ht]
      rfl

end ThresholdHC.BlindUpper
