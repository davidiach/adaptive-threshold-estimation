import ScheduledBounds
import OrderedBayes

namespace PilotFeedback.Stopping
open Ordered ThresholdHC.SharpRMS

/-- Legal actions at absolute follow-up position k. -/
def menu (j k : ℕ) : List Mode :=
  [none] ++ (if k<j then [some true] else []) ++ (if k<18-j then [some false] else [])

def plans (j : ℕ) : ℕ → ℕ → List (List Mode)
  | 0, _ => [[]]
  | n+1, k => (menu j k).flatMap fun m => (plans j n (k+1)).map (m :: ·)

theorem modes_mem (B : Schedule) (v : List Bool) (n k : ℕ) :
    modes B v n k ∈ plans (v.count true) n k := by
  induction n generalizing k with
  | zero => simp [modes,plans]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨effective B v k, ?_, List.mem_map.mpr ⟨_, ih (k+1), rfl⟩⟩
    unfold effective Pilot.choice
    cases h : B v k with
    | none => simp [menu]
    | some b => cases b <;> simp [Pilot.available,menu] <;> omega

/-- With the update still available, take the lesser of committing now and
following the next prescribed action, keeping the trigger available to both children.
At the final position every possible move is already a committed suffix. -/
def unused (j : ℕ) : List Mode → ℕ → Weights → ℕ
  | [], k, w => Scheduled.tailCost j k w
  | m::ms, k, w => min (Scheduled.tailCost j k w)
      (unused j ms (k+1) (advance w m false) + unused j ms (k+1) (advance w m true))

def floorRow (j : ℕ) : ℕ :=
  [1404278950786292244,974345025231250304,662039274152383219,441325711876518097,
   292821378530636801,199889013807594716,147482344772790146,122390596188468196,
   114184338247564930,112589634151791975,114184338247564930,122390596188468196,
   147482344772790146,199889013807594716,292821378530636801,441325711876518097,
   662039274152383219,974345025231250304,1404278950786292244][j]?.getD 0

def rowCheck (j : ℕ) : Bool := (plans j 6 0).all fun ms =>
  decide (floorRow j ≤ unused j ms 0 (pilotWeights 18 j))

def pilotSum : ℕ → ℕ → ℕ
  | 0, j => floorRow j
  | n+1, j => pilotSum n j + pilotSum n (j+1)

end PilotFeedback.Stopping
