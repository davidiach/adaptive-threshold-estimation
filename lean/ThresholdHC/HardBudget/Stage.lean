import ThresholdHC.HardBudget.Words

noncomputable section
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper

def decode (pol : List Bool → Option ℕ) : List Bool → Option (List Bool)
  | [] => if pol [] = none then some [] else none
  | b::w => if pol [] = none then some [] else
      (decode (fun xs => pol (b::xs)) w).map (b::·)

private theorem cons_history (x y : ProcessTape) (b : Bool) (hx : x 0 = some b)
    (hy : ∀ k, x (k+1) = y k) (n : ℕ) :
    processHistory x (n+1) = b::processHistory y n := by
  unfold processHistory
  rw [List.ofFn_succ]
  change List.filterMap id (x 0 :: List.ofFn (fun i : Fin n => x (i.val+1))) = _
  simp [hx,hy]
  rfl

/-- A successful decode recovers exactly the original stopped tape. If the
last observation just completed the run, its final output is retained. -/
theorem decode_correct (pol : List Bool → Option ℕ) (n : ℕ) (s : Table) :
    let x := populationPath pol s
    match decode pol (readBlock n (fun h => (pol h).getD 0) s).1 with
    | none => pol (processHistory x n) ≠ none
    | some w => pol (processHistory x n) = none ∧ x = fun k => w[k]? := by
  dsimp only
  induction n generalizing pol s with
  | zero =>
    have hh : processHistory (populationPath pol s) 0 = [] := by simp [processHistory]
    by_cases hp : pol [] = none
    · simp only [readBlock,decode,hp,ite_true,hh,true_and]
      exact populationPath_none pol s hp
    · simp [readBlock,decode,hp,hh]
  | succ n ih =>
    cases hp : pol [] with
    | none =>
      have hx := populationPath_none pol s hp
      simp [readBlock,decode,hp,hx,processHistory,processPrefix]
    | some i =>
      let b := s i 0
      let p := fun xs => pol (b::xs)
      let t := Function.update s i (tapeDrop 1 (s i))
      let x := populationPath pol s
      let y := populationPath p t
      have hx : x 0 = some b := by rw [show x 0 = _ from populationPath_zero pol s,hp]; rfl
      have hy (k : ℕ) : x (k+1) = y k := populationPath_succ pol s i k hp
      have hh := cons_history x y b hx hy n
      let w := (readBlock n (fun h => (p h).getD 0) t).1
      have hread : (readBlock (n+1) (fun h => (pol h).getD 0) s).1 = b::w := by simp [readBlock,hp,b,w,t,p]
      rw [hread]
      simp only [decode,hp,reduceCtorEq,ite_false]
      have h := ih p t
      change (match decode p w with
        | none => p (processHistory y n) ≠ none
        | some u => p (processHistory y n) = none ∧ y = fun k => u[k]?) at h
      change (match (decode p w).map (b::·) with
        | none => pol (processHistory x (n+1)) ≠ none
        | some u => pol (processHistory x (n+1)) = none ∧ x = fun k => u[k]?)
      cases hd : decode p w with
      | none => rw [hd] at h; simpa only [Option.map_none,hh] using h
      | some u =>
        rw [hd] at h
        refine ⟨?_,?_⟩
        · rw [hh]; exact h.1
        · funext k; cases k with
          | zero => exact hx
          | succ k => exact (hy k).trans (congrFun h.2 k)

def stageOutput {R : Type} [m : MeasurableSpace R] (A : AdaptiveEstimator R)
    (M : ℝ) (r : R) (w : List Bool) : Option ℝ :=
  (decode (A.policy r) w).map (fun v => clipEstimate M (A.output (r,fun k => v[k]?)))

theorem stageOutput_correct {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (M : ℝ) (n : ℕ) (r : R) (s : Table) :
    stageOutput A M r (readBlock n (fun h => (A.policy r h).getD 0) s).1 =
      stageResult A n M r s := by
  unfold stageOutput stageResult
  have h := decode_correct (A.policy r) n s
  cases hx : decode (A.policy r) (readBlock n (fun h => (A.policy r h).getD 0) s).1 with
  | none => rw [hx] at h; simp [h]
  | some w => rw [hx] at h; rw [ite_eq_left h.1,h.2]; rfl

end ThresholdHC.HardBudget
