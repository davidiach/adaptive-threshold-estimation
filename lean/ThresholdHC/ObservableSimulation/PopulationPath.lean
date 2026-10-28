import ThresholdHC.CriticalEntropy.PopulationTapeLaw
import ThresholdHC.Tier4.Model

noncomputable section

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3

theorem populationSimulation_consistent {I : Type} [DecidableEq I]
    (m n : ℕ) (h : m ≤ n) (pol : List Bool → Option I) (s : I → ℕ → Bool)
    (i : Fin m) :
    (populationSimulation pol n s).2 ⟨i.val,lt_of_lt_of_le i.isLt h⟩ =
      (populationSimulation pol m s).2 i := by
  induction m generalizing n pol s with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases hp : pol [] with
      | none => simp [populationSimulation,hp]
      | some j =>
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [populationSimulation,hp]
        · simp only [populationSimulation,hp,Fin.cons_succ]
          change (populationSimulation (fun xs => pol (s j 0::xs)) n
            (Function.update s j (tapeDrop 1 (s j)))).2
              ⟨k.val,lt_of_lt_of_le k.isLt (Nat.le_of_succ_le_succ h)⟩ = _
          exact ih n (Nat.le_of_succ_le_succ h) (fun xs => pol (s j 0::xs))
            (Function.update s j (tapeDrop 1 (s j))) k

def populationPath {I : Type} [DecidableEq I]
    (pol : List Bool → Option I) (s : I → ℕ → Bool) : ProcessTape :=
  fun k => (populationSimulation pol (k+1) s).2 ⟨k,Nat.lt_succ_self k⟩

theorem populationPath_prefix {I : Type} [DecidableEq I]
    (pol : List Bool → Option I) (s : I → ℕ → Bool) (n : ℕ) :
    processPrefix n (populationPath pol s) = (populationSimulation pol n s).2 := by
  funext i
  exact (populationSimulation_consistent (i.val+1) n (Nat.succ_le_of_lt i.isLt) pol s
    ⟨i.val,Nat.lt_succ_self i.val⟩).symm

theorem measurable_populationPath {I : Type} [DecidableEq I]
    (pol : List Bool → Option I) : Measurable (populationPath pol) :=
  Measurable.of_eval (fun k =>
    (measurable_pi_apply (⟨k,Nat.lt_succ_self k⟩ : Fin (k+1))).comp
      (measurable_populationSimulation_word (k+1) pol))

end ThresholdHC.ObservableSimulation

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3

local instance simulationOptionSpace (I : Type) : MeasurableSpace (Option I) := ⊤

theorem measurable_seeded_populationSimulation {R I : Type}
    [MeasurableSpace R] [DecidableEq I] [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (n : ℕ) (pol : R → List Bool → Option I)
    (hp : ∀ xs, Measurable (fun r => pol r xs)) :
    Measurable (fun z : R × (I → ℕ → Bool) => (populationSimulation (pol z.1) n z.2).2) := by
  induction n generalizing pol with
  | zero => exact measurable_const
  | succ n ih =>
    let f (o : Option I) (z : R × (I → ℕ → Bool)) : Fin (n+1) → Option Bool :=
      match o with
      | none => fun _ => none
      | some j => Fin.cons (some (z.2 j 0))
          (populationSimulation (fun xs => pol z.1 (z.2 j 0::xs)) n
            (Function.update z.2 j (tapeDrop 1 (z.2 j)))).2
    have hf (o : Option I) : Measurable (f o) := by
      cases o with
      | none => exact measurable_const
      | some j =>
        let g (b : Bool) (z : R × (I → ℕ → Bool)) : Fin (n+1) → Option Bool :=
          Fin.cons (some b) (populationSimulation (fun xs => pol z.1 (b::xs)) n
            (Function.update z.2 j (tapeDrop 1 (z.2 j)))).2
        have hupd : Measurable (fun z : R × (I → ℕ → Bool) =>
            Function.update z.2 j (tapeDrop 1 (z.2 j))) :=
          measurable_update'.comp (measurable_snd.prodMk
            ((measurable_tapeDrop 1).comp ((measurable_pi_apply j).comp measurable_snd)))
        have hg (b : Bool) : Measurable (g b) :=
          (measurable_of_countable (fun w : Fin n → Option Bool =>
            (Fin.cons (some b) w : Fin (n+1) → Option Bool))).comp
              ((ih (fun r xs => pol r (b::xs)) (fun xs => hp (b::xs))).comp
                (measurable_fst.prodMk hupd))
        have hsel : Measurable (fun z : Bool × (R × (I → ℕ → Bool)) => g z.1 z.2) :=
          measurable_from_prod_countable_right hg
        have hb : Measurable (fun z : R × (I → ℕ → Bool) => z.2 j 0) :=
          (measurable_pi_apply 0).comp ((measurable_pi_apply j).comp measurable_snd)
        exact hsel.comp (hb.prodMk measurable_id)
    have hsel : Measurable (fun z : Option I × (R × (I → ℕ → Bool)) => f z.1 z.2) :=
      measurable_from_prod_countable_right hf
    have h := hsel.comp (((hp []).comp measurable_fst).prodMk measurable_id)
    convert h using 1
    funext z
    cases ho : pol z.1 [] <;> simp [populationSimulation,f,ho]

theorem measurable_seeded_populationPath {R I : Type}
    [MeasurableSpace R] [DecidableEq I] [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (pol : R → List Bool → Option I)
    (hp : ∀ xs, Measurable (fun r => pol r xs)) :
    Measurable (fun z : R × (I → ℕ → Bool) => populationPath (pol z.1) z.2) :=
  Measurable.of_eval (fun k =>
    (measurable_pi_apply (⟨k,Nat.lt_succ_self k⟩ : Fin (k+1))).comp
      (measurable_seeded_populationSimulation (k+1) pol hp))

end ThresholdHC.ObservableSimulation
