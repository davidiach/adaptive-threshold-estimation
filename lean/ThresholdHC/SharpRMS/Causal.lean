import ThresholdHC.ContinuousObserved.Prefix
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! A causal channel on each coin tape composes with every adaptive policy. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 CriticalEntropy ObservableSimulation ContinuousObserved

def localHistory {I : Type} [DecidableEq I] (pol : List Bool → Option I) :
    List Bool → I → List Bool
  | [], _ => []
  | b::bs, j =>
    (if pol [] = some j then [b] else []) ++ localHistory (fun xs => pol (b::xs)) bs j

def localResponse {I : Type} [DecidableEq I] (pol : List Bool → Option I)
    (g : I → List Bool → Bool → Bool) (xs : List Bool) (y : Bool) : Bool :=
  match pol xs with
  | none => y
  | some j => g j (localHistory pol xs j) y

def transformTape (g : List Bool → Bool → Bool) (raw : ℕ → Bool) : ℕ → Bool
  | 0 => g [] (raw 0)
  | n+1 => transformTape (fun ys => g (g [] (raw 0)::ys)) (tapeDrop 1 raw) n

private theorem tail_transform (g : List Bool → Bool → Bool) (raw : ℕ → Bool) :
    tapeDrop 1 (transformTape g raw) = transformTape (fun ys => g (g [] (raw 0)::ys)) (tapeDrop 1 raw) := by
  funext n
  unfold tapeDrop
  rw [show 1+n=n+1 by omega]
  rfl

private theorem prefix_causal {I : Type} [DecidableEq I] (n : ℕ) (pol : List Bool → Option I)
    (g : I → List Bool → Bool → Bool) (raw : I → ℕ → Bool) :
    decodePrefix (localResponse pol g)
      (populationSimulation (fun xs => pol (decode (localResponse pol g) xs)) n raw).2 =
      (populationSimulation pol n (fun i => transformTape (g i) (raw i))).2 := by
  induction n generalizing pol g raw with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    cases hi : pol [] with
    | none => simp [populationSimulation,decode,hi,decodePrefix_none]
    | some i =>
      let b := raw i 0
      let c := g i [] b
      let pol' := fun xs => pol (c::xs)
      let g' := Function.update g i (fun ys => g i (c::ys))
      let r' := Function.update raw i (tapeDrop 1 (raw i))
      have root : localResponse pol g [] b = c := by simp [localResponse,localHistory,hi,c]
      have step : (fun ys => localResponse pol g (c::ys)) = localResponse pol' g' := by
        funext ys y
        unfold localResponse
        change (match pol' ys with | none => y | some j => g j (localHistory pol (c::ys) j) y) = _
        cases action : pol' ys with
        | none => rfl
        | some j =>
          by_cases e : j=i
          · subst j
            simp [localHistory,hi,pol',g']
          · simp [localHistory,hi,pol',g',e,Ne.symm e]
      have tapes : (fun j => transformTape (g' j) (r' j)) =
          Function.update (fun j => transformTape (g j) (raw j)) i (tapeDrop 1 (transformTape (g i) (raw i))) := by
        funext j
        by_cases e : j=i
        · subst j
          simp [g',r',tail_transform,c,b]
        · simp [g',r',e]
      simp only [populationSimulation,decode,hi,decodePrefix_cons_some]
      change (Fin.cons (some (localResponse pol g [] b))
        (decodePrefix (fun ys => localResponse pol g (localResponse pol g [] b::ys))
          (populationSimulation (fun xs => pol (decode (localResponse pol g) (b::xs))) n r').2) : Prefix (n+1)) =
        (Fin.cons (some c) (populationSimulation pol' n (Function.update (fun j => transformTape (g j) (raw j)) i (tapeDrop 1 (transformTape (g i) (raw i))))).2 : Prefix (n+1))
      simp only [decode,root,step]
      rw [show (fun xs => pol (c::decode (localResponse pol' g') xs)) = (fun xs => pol' (decode (localResponse pol' g') xs)) from rfl,
        ih pol' g' r',tapes]

/-- Decoding the observed source tape gives precisely the same infinite stopped
path as first transforming each coin's entire tape and then running the target
policy. No bound on creation, revisiting, interleaving, or stopping is needed. -/
theorem causal_population_path {I : Type} [DecidableEq I] (pol : List Bool → Option I)
    (g : I → List Bool → Bool → Bool) (raw : I → ℕ → Bool) :
    decodeTape (localResponse pol g)
        (populationPath (fun xs => pol (decode (localResponse pol g) xs)) raw) =
      populationPath pol (fun i => transformTape (g i) (raw i)) := by
  have prefixes (n : ℕ) := prefix_causal n pol g raw
  funext n
  have eq := prefixes (n+1)
  rw [←populationPath_prefix,decodePrefix_processPrefix,←populationPath_prefix] at eq
  exact congrFun eq (Fin.last n)

theorem measurable_transformTape {R : Type} [MeasurableSpace R]
    (g : R → List Bool → Bool → Bool) (hm : ∀ xs b, Measurable (fun r => g r xs b)) :
    Measurable (fun z : R × (ℕ → Bool) => transformTape (g z.1) z.2) := by
  apply Measurable.of_eval
  intro n
  induction n generalizing g with
  | zero =>
    have hb : Measurable (fun z : Bool × R => g z.2 [] z.1) := measurable_from_prod_countable_right (hm [])
    change Measurable (fun z : R × (ℕ → Bool) => g z.1 [] (z.2 0))
    have hpair : Measurable (fun z : R × (ℕ → Bool) => (z.2 0,z.1)) :=
      ((measurable_pi_apply 0).comp measurable_snd).prodMk measurable_fst
    exact hb.comp hpair
  | succ n ih =>
    have branch (b : Bool) : Measurable (fun z : R × (ℕ → Bool) =>
        transformTape (fun xs => g z.1 (b::xs)) (tapeDrop 1 z.2) n) :=
      (ih (fun r xs => g r (b::xs)) (fun xs => hm (b::xs))).comp
        (measurable_fst.prodMk ((measurable_tapeDrop 1).comp measurable_snd))
    have choose : Measurable (fun z : Bool × (R × (ℕ → Bool)) =>
        transformTape (fun xs => g z.2.1 (z.1::xs)) (tapeDrop 1 z.2.2) n) :=
      measurable_from_prod_countable_right branch
    have hb : Measurable (fun z : Bool × R => g z.2 [] z.1) := measurable_from_prod_countable_right (hm [])
    have bit : Measurable (fun z : R × (ℕ → Bool) => g z.1 [] (z.2 0)) :=
      hb.comp (show Measurable (fun z : R × (ℕ → Bool) => (z.2 0,z.1)) from
        ((measurable_pi_apply 0).comp measurable_snd).prodMk measurable_fst)
    exact choose.comp (bit.prodMk measurable_id)

theorem measurable_localHistory {R : Type} [MeasurableSpace R]
    (pol : R → List Bool → Option ℕ) (hp : Tier5.MeasurableCreationPolicy pol) (xs : List Bool) (j : ℕ) :
    Measurable (fun r => localHistory (pol r) xs j) := by
  induction xs generalizing pol with
  | nil => exact measurable_const
  | cons b bs ih =>
    have h := ih (fun r ys => pol r (b::ys)) (fun ys => hp (b::ys))
    have z : Measurable (fun r => if pol r []=some j then [b] else []) :=
      Measurable.ite (hp [] (some j)) measurable_const measurable_const
    exact (measurable_of_countable (fun x : List Bool × List Bool => x.1++x.2)).comp (z.prodMk h)

theorem measurable_localResponse {R : Type} [MeasurableSpace R]
    (pol : R → List Bool → Option ℕ) (hp : Tier5.MeasurableCreationPolicy pol)
    (g : R → ℕ → List Bool → Bool → Bool) (hg : ∀ i xs b, Measurable (fun r => g r i xs b))
    (xs : List Bool) (y : Bool) : Measurable (fun r => localResponse (pol r) (g r) xs y) := by
  let F (o : Option ℕ) (r : R) := match o with
    | none => y | some i => g r i (localHistory (pol r) xs i) y
  have h (o) : Measurable (F o) := by
    cases o with
    | none => exact measurable_const
    | some i =>
      have hb : Measurable (fun z : List Bool × R => g z.2 i z.1 y) :=
        measurable_from_prod_countable_right (fun ys => hg i ys y)
      exact hb.comp ((measurable_localHistory pol hp xs i).prodMk measurable_id)
  have ho : Measurable (fun r => pol r xs) := measurable_to_countable' (hp xs)
  have m : Measurable (fun z : Option ℕ × R => F z.1 z.2) := measurable_from_prod_countable_right h
  convert m.comp (ho.prodMk measurable_id) using 1
  funext r
  cases h : pol r xs <;> simp [F,localResponse,h]

end ThresholdHC.SharpRMS
