import ThresholdHC.CriticalEntropy.PopulationTapeLaw
import ThresholdHC.Tier5.CreationBase

noncomputable section

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.Proofs

theorem populationSimulation_word_embed {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I → J) (he : Function.Injective e) (n : ℕ)
    (polI : List Bool → Option I) (polJ : List Bool → Option J)
    (hp : ∀ xs, xs.length < n → polJ xs = (polI xs).map e)
    (s : J → ℕ → Bool) :
    (populationSimulation polJ n s).2 = (populationSimulation polI n (s ∘ e)).2 := by
  induction n generalizing polI polJ s with
  | zero => rfl
  | succ n ih =>
    have hzero := hp [] (by simp)
    cases hi : polI [] with
    | none => simp only [hi,Option.map_none] at hzero; simp [populationSimulation,hi,hzero]
    | some j =>
      simp only [hi,Option.map_some] at hzero
      simp only [populationSimulation,hi,hzero,Function.comp_apply]
      congr 1
      have hu : (Function.update s (e j) (tapeDrop 1 (s (e j)))) ∘ e =
          Function.update (s ∘ e) j (tapeDrop 1 (s (e j))) := by
        funext i
        by_cases h : i = j
        · subst i; simp
        · simp [Function.comp_def,h,he.ne h]
      have ht := ih (fun xs => polI (s (e j) 0::xs))
        (fun xs => polJ (s (e j) 0::xs))
        (fun xs hx => hp _ (by simp only [List.length_cons]; omega))
        (Function.update s (e j) (tapeDrop 1 (s (e j))))
      simpa only [hu] using ht

theorem selected_history_lt_coinCap (pol : List Bool → Option ℕ)
    (n : ℕ) (xs : List Bool) (hx : xs.length < n) (i : ℕ) (hi : pol xs = some i) :
    i < Tier5.coinCap n pol := by
  let v : Fin xs.length → Option Bool := fun t => some (xs.get t)
  have hv : fullHist v = xs := by
    simp [fullHist,v,← List.map_ofFn]
  have hh : pol (ThresholdHC.histBefore (Fin.snoc v none) (Fin.last xs.length)) = some i := by
    simpa only [histBefore_snoc_last,hv] using hi
  exact (Tier5.selected_lt_coinCap pol (Fin.snoc v none) (Fin.last xs.length) i hh).trans_le
    (Tier5.coinCap_mono pol (Nat.succ_le_of_lt hx))

theorem populationSimulation_cap (n : ℕ) (pol : List Bool → Option ℕ)
    (s : ℕ → ℕ → Bool) :
    (populationSimulation pol n s).2 =
      (populationSimulation (Tier5.capPolicy (Tier5.coinCap n pol) pol) n
        (fun i => s i.val)).2 := by
  apply populationSimulation_word_embed Fin.val Fin.val_injective
  intro xs hx
  cases hi : pol xs with
  | none => simp [Tier5.capPolicy,hi]
  | some i =>
    have hb := selected_history_lt_coinCap pol n xs hx i hi
    simp [Tier5.capPolicy,hi,hb]

end ThresholdHC.ObservableSimulation
