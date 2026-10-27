import ThresholdHC.CriticalEntropy.CriticalCommonPair

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

local instance : MeasurableSpace (Option Bool) := ⊤

/-- Simulate a finite population horizon, charging only queries to label i.
All other labels use auxiliary tapes. No magnitude or sign enters the rule. -/
def localSimulation {I : Type} [DecidableEq I] (i : I)
    (pol : List Bool → Option I) :
    (n : ℕ) → (I → ℕ → Bool) → (ℕ → Bool) → ℕ × (Fin n → Option Bool)
  | 0, _, _ => (0, Fin.elim0)
  | n+1, s, ω =>
    match pol [] with
    | none => (0, fun _ => none)
    | some j =>
      if j=i then
        let v := localSimulation i (fun xs => pol (ω 0::xs)) n s (tapeDrop 1 ω)
        (v.1+1, Fin.cons (some (ω 0)) v.2)
      else
        let v := localSimulation i (fun xs => pol (s j 0::xs)) n
          (Function.update s j (tapeDrop 1 (s j))) ω
        (v.1, Fin.cons (some (s j 0)) v.2)

theorem localSimulation_count_le {I : Type} [DecidableEq I] (i : I)
    (n : ℕ) (pol : List Bool → Option I) (s : I → ℕ → Bool) (ω : ℕ → Bool) :
    (localSimulation i pol n s ω).1 ≤ n := by
  induction n generalizing pol s ω with
  | zero => simp [localSimulation]
  | succ n ih =>
    simp only [localSimulation]
    split
    · simp
    · split_ifs
      · exact Nat.add_le_add_right (ih _ _ _) 1
      · exact (ih _ _ _).trans (Nat.le_succ n)

/-- The complete simulated transcript is determined by exactly the genuine
coin flips charged by the simulation, even when other coins are interleaved. -/
theorem localSimulation_prefix_ext {I : Type} [DecidableEq I] (i : I)
    (n : ℕ) (pol : List Bool → Option I) (s : I → ℕ → Bool) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (localSimulation i pol n s ω).1 ω =
      Tier2.tapePrefix (localSimulation i pol n s ω).1 ω') :
    localSimulation i pol n s ω = localSimulation i pol n s ω' := by
  induction n generalizing pol s ω ω' with
  | zero => rfl
  | succ n ih =>
    cases hp : pol [] with
    | none => simp [localSimulation,hp]
    | some j =>
      by_cases hji : j=i
      · rw [localSimulation,hp] at h ⊢
        dsimp only at h ⊢
        rw [ite_eq_left hji] at h
        simp only [ite_eq_left hji]
        have hhead : ω 0 = ω' 0 := by
          exact congrFun h ⟨0, Nat.zero_lt_succ _⟩
        have htail := prefix_eq_drop (k := 1)
          (m := (localSimulation i (fun xs => pol (ω 0::xs)) n s (tapeDrop 1 ω)).1)
          h (by omega)
        have heq := ih (fun xs => pol (ω 0::xs)) s (tapeDrop 1 ω) (tapeDrop 1 ω') htail
        rw [localSimulation,hp]
        simp only [ite_eq_left hji]
        rw [← hhead,heq]
      · rw [localSimulation,hp] at h ⊢
        dsimp only at h ⊢
        rw [ite_eq_right hji] at h
        simp only [ite_eq_right hji]
        rw [localSimulation,hp]
        simp only [ite_eq_right hji]
        rw [ih _ _ _ _ h]

theorem measurable_localSimulation {I : Type} [DecidableEq I] (i : I)
    (n : ℕ) (pol : List Bool → Option I) :
    Measurable (fun z : (I → ℕ → Bool) × (ℕ → Bool) => localSimulation i pol n z.1 z.2) := by
  induction n generalizing pol with
  | zero => exact measurable_const
  | succ n ih =>
    cases hp : pol [] with
    | none => simpa only [localSimulation,hp] using
        (measurable_const : Measurable (fun _ : (I → ℕ → Bool) × (ℕ → Bool) =>
          (0,fun _ : Fin (n+1) => (none : Option Bool))))
    | some j =>
      by_cases hji : j=i
      · let f (b : Bool) (z : (I → ℕ → Bool) × (ℕ → Bool)) : ℕ × (Fin (n+1) → Option Bool) :=
          let v := localSimulation i (fun xs => pol (b::xs)) n z.1 (tapeDrop 1 z.2)
          (v.1+1,Fin.cons (some b) v.2)
        have hf (b : Bool) : Measurable (f b) :=
          (measurable_of_countable (fun v : ℕ × (Fin n → Option Bool) =>
            (v.1+1,(Fin.cons (some b) v.2 : Fin (n+1) → Option Bool)))).comp
            ((ih (fun xs => pol (b::xs))).comp
              (measurable_fst.prodMk ((measurable_tapeDrop 1).comp measurable_snd)))
        have hsel : Measurable (fun z : Bool × ((I → ℕ → Bool) × (ℕ → Bool)) => f z.1 z.2) :=
          measurable_from_prod_countable_right hf
        have hb : Measurable (fun z : (I → ℕ → Bool) × (ℕ → Bool) => z.2 0) :=
          (measurable_pi_apply 0).comp measurable_snd
        have h := hsel.comp (hb.prodMk measurable_id)
        simpa only [localSimulation,hp,ite_eq_left hji,f,Function.comp_def,id_eq] using h
      · let f (b : Bool) (z : (I → ℕ → Bool) × (ℕ → Bool)) : ℕ × (Fin (n+1) → Option Bool) :=
          let v := localSimulation i (fun xs => pol (b::xs)) n
            (Function.update z.1 j (tapeDrop 1 (z.1 j))) z.2
          (v.1,Fin.cons (some b) v.2)
        have hupd : Measurable (fun z : (I → ℕ → Bool) × (ℕ → Bool) =>
            Function.update z.1 j (tapeDrop 1 (z.1 j))) :=
          measurable_update'.comp (measurable_fst.prodMk
            ((measurable_tapeDrop 1).comp ((measurable_pi_apply j).comp measurable_fst)))
        have hf (b : Bool) : Measurable (f b) :=
          (measurable_of_countable (fun v : ℕ × (Fin n → Option Bool) =>
            (v.1,(Fin.cons (some b) v.2 : Fin (n+1) → Option Bool)))).comp
            ((ih (fun xs => pol (b::xs))).comp (hupd.prodMk measurable_snd))
        have hsel : Measurable (fun z : Bool × ((I → ℕ → Bool) × (ℕ → Bool)) => f z.1 z.2) :=
          measurable_from_prod_countable_right hf
        have hb : Measurable (fun z : (I → ℕ → Bool) × (ℕ → Bool) => z.1 j 0) :=
          (measurable_pi_apply 0).comp ((measurable_pi_apply j).comp measurable_fst)
        have h := hsel.comp (hb.prodMk measurable_id)
        simpa only [localSimulation,hp,ite_eq_right hji,f,Function.comp_def,id_eq] using h

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
local instance : MeasurableSpace (Option Bool) := ⊤

def localSimulationProcedure {I : Type} [DecidableEq I] (i : I)
    (n : ℕ) (pol : List Bool → Option I) :
    StoppedProcedure (I → ℕ → Bool) (Fin n → Option Bool) where
  stop := fun z => ((localSimulation i pol n z.1 z.2).1 : ℕ∞)
  output := fun z => (localSimulation i pol n z.1 z.2).2
  measurable_stop := (measurable_of_countable (fun k : ℕ => (k : ℕ∞))).comp
    (measurable_localSimulation i n pol).fst
  measurable_output := (measurable_localSimulation i n pol).snd
  stopPrefix := fun k => {z | (localSimulation i pol n z.1 (completePrefix k z.2)).1 = k}
  measurable_stopPrefix := fun k =>
    (((measurable_localSimulation i n pol).comp
      (measurable_fst.prodMk ((measurable_completePrefix k).comp measurable_snd))).fst)
        (measurableSet_singleton k)
  stop_observable := by
    intro k z
    change (localSimulation i pol n z.1 (completePrefix k (Tier2.tapePrefix k z.2))).1 = k ↔
      ((localSimulation i pol n z.1 z.2).1 : ℕ∞) = k
    constructor
    · intro hk
      have heq := localSimulation_prefix_ext i n pol z.1
        (completePrefix k (Tier2.tapePrefix k z.2)) z.2
        (by rw [hk]; exact tapePrefix_completePrefix k _)
      exact_mod_cast (congrArg Prod.fst heq).symm.trans hk
    · intro hk
      have hk' : (localSimulation i pol n z.1 z.2).1 = k := by exact_mod_cast hk
      have heq := localSimulation_prefix_ext i n pol z.1 z.2
        (completePrefix k (Tier2.tapePrefix k z.2))
        (by rw [hk']; exact (tapePrefix_completePrefix k _).symm)
      exact (congrArg Prod.fst heq).symm.trans hk'
  outputPrefix := fun k z => (localSimulation i pol n z.1 (completePrefix k z.2)).2
  measurable_outputPrefix := fun k =>
    ((measurable_localSimulation i n pol).comp
      (measurable_fst.prodMk ((measurable_completePrefix k).comp measurable_snd))).snd
  output_observable := by
    intro k z hk
    have hk' : (localSimulation i pol n z.1 z.2).1 = k := by exact_mod_cast hk
    exact congrArg Prod.snd (localSimulation_prefix_ext i n pol z.1 z.2
      (completePrefix k (Tier2.tapePrefix k z.2))
      (by rw [hk']; exact (tapePrefix_completePrefix k _).symm))

theorem localSimulationProcedure_capped {I : Type} [DecidableEq I] (i : I)
    (n : ℕ) (pol : List Bool → Option I) (z : (I → ℕ → Bool) × (ℕ → Bool)) :
    (localSimulationProcedure i n pol).stop z ≤ n := by
  change ((localSimulation i pol n z.1 z.2).1 : ℕ∞) ≤ (n : ℕ∞)
  exact_mod_cast localSimulation_count_le i n pol z.1 z.2

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
local instance : MeasurableSpace (Option Bool) := ⊤

/-- The full finite-horizon simulation records each label's flip count. -/
def populationSimulation {I : Type} [DecidableEq I]
    (pol : List Bool → Option I) :
    (n : ℕ) → (I → ℕ → Bool) → (I → ℕ) × (Fin n → Option Bool)
  | 0, _ => (fun _ => 0, Fin.elim0)
  | n+1, s =>
    match pol [] with
    | none => (fun _ => 0,fun _ => none)
    | some j =>
      let v := populationSimulation (fun xs => pol (s j 0::xs)) n
        (Function.update s j (tapeDrop 1 (s j)))
      (fun i => v.1 i+if j=i then 1 else 0,Fin.cons (some (s j 0)) v.2)

theorem localSimulation_eq_population {I : Type} [DecidableEq I] (i : I)
    (n : ℕ) (pol : List Bool → Option I) (s : I → ℕ → Bool) (ω : ℕ → Bool) :
    localSimulation i pol n s ω =
      ((populationSimulation pol n (Function.update s i ω)).1 i,
        (populationSimulation pol n (Function.update s i ω)).2) := by
  induction n generalizing pol s ω with
  | zero => rfl
  | succ n ih =>
    cases hp : pol [] with
    | none => simp [localSimulation,populationSimulation,hp]
    | some j =>
      by_cases hji : j=i
      · subst j
        simp only [localSimulation,populationSimulation,hp,ite_true,
          Function.update_self,Function.update_idem]
        rw [ih]
      · simp only [localSimulation,populationSimulation,hp,ite_eq_right hji,
          Function.update_of_ne hji,add_zero]
        rw [ih,Function.update_comm hji]

theorem populationSimulation_total_work {I : Type} [DecidableEq I] [Fintype I]
    (n : ℕ) (pol : List Bool → Option I) (s : I → ℕ → Bool) :
    (∑ i, (populationSimulation pol n s).1 i) =
      ∑ t : Fin n, if ((populationSimulation pol n s).2 t).isSome then 1 else 0 := by
  induction n generalizing pol s with
  | zero => simp [populationSimulation]
  | succ n ih =>
    cases hp : pol [] with
    | none => simp [populationSimulation,hp]
    | some j =>
      simp only [populationSimulation,hp]
      rw [Finset.sum_add_distrib,Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,Option.isSome_some,ite_true]
      rw [ih]
      have hone : (∑ i : I, if j=i then 1 else 0 : ℕ) = 1 := by simp
      rw [hone]
      omega

theorem localSimulation_total_work {I : Type} [DecidableEq I] [Fintype I]
    (n : ℕ) (pol : List Bool → Option I) (s : I → ℕ → Bool) :
    (∑ i, (localSimulation i pol n s (s i)).1) =
      ∑ t : Fin n, if ((populationSimulation pol n s).2 t).isSome then 1 else 0 := by
  simp_rw [localSimulation_eq_population,Function.update_eq_self]
  exact populationSimulation_total_work n pol s

end ThresholdHC.CriticalEntropy
