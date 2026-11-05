import ThresholdHC.ObservableSimulation.PopulationPath
import ThresholdHC.Tier3.StoppingBase

noncomputable section
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

theorem populationSimulation_valid {I : Type} [DecidableEq I]
    (n : ℕ) (pol : List Bool → Option I) (s : I → ℕ → Bool) (t : Fin n) :
    ((populationSimulation pol n s).2 t).isSome =
      (pol (histBefore (populationSimulation pol n s).2 t)).isSome := by
  induction n generalizing pol s with
  | zero => exact Fin.elim0 t
  | succ n ih =>
    cases hp : pol [] with
    | none =>
      simp [populationSimulation,hp,histBefore]
    | some j =>
      refine Fin.cases ?_ (fun k => ?_) t
      · simp [populationSimulation,hp,histBefore_cons_zero]
      · simp only [populationSimulation,hp,Fin.cons_succ,histBefore_cons_succ,
          Option.toList_some,List.singleton_append]
        exact ih (fun xs => pol (s j 0::xs)) (Function.update s j (tapeDrop 1 (s j))) k

theorem populationPath_valid {I : Type} [DecidableEq I]
    (pol : List Bool → Option I) (s : I → ℕ → Bool) (n : ℕ) :
    (populationPath pol s n).isSome =
      (pol (processHistory (populationPath pol s) n)).isSome := by
  have h := populationSimulation_valid (n+1) pol s (Fin.last n)
  rw [← populationPath_prefix] at h
  simpa only [histBefore_processPrefix_last,processPrefix,Fin.val_last] using h

end ThresholdHC.TypedConfidence
