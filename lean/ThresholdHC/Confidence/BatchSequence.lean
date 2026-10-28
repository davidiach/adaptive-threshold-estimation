import ThresholdHC.Confidence.BatchLift

noncomputable section
set_option maxHeartbeats 1200000
namespace ThresholdHC.Confidence
open ThresholdHC.BlindUpper

def prefixState {m : ℕ} (n : ℕ) (final : RepeatState m) : RepeatState m :=
  fun i => if i.val < n then final i else batchInitial

/-- Concatenating all legal local executions gives one legal observable
execution, with exactly the sum of their actual lengths. -/
theorem repeat_all_consumes (m L : ℕ) (r : RepeatSeed) (s : ℕ → ℕ → Bool)
    (words : MedianIndex m → List Bool) (final : RepeatState m)
    (hstop : ∀ i, controlLabel (final i).1 = none)
    (hlocal : ∀ i, ∃ t, BatchConsumes L (r i.val) batchInitial
      (fun j => s (Nat.pair i.val j)) (words i) (final i) t) :
    ∃ xs t, RepeatConsumes m L r (repeatInitial m) s xs final t ∧
      xs.length = ∑ i, (words i).length := by
  classical
  have H : ∀ n, n ≤ 2*m+1 → ∃ xs t,
      RepeatConsumes m L r (repeatInitial m) s xs (prefixState n final) t ∧
      (∀ i : MedianIndex m, n ≤ i.val → ∀ j, t (Nat.pair i.val j) = s (Nat.pair i.val j)) ∧
      xs.length = ∑ i ∈ Finset.univ.filter (fun i : MedianIndex m => i.val < n), (words i).length := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨[],s, ?_, fun _ _ _ => rfl, by simp⟩
      have he : prefixState 0 final = repeatInitial m := by funext i; simp [prefixState,repeatInitial]
      rw [he]
      exact .nil _ _
    | succ n ih =>
      intro hn
      obtain ⟨xs,t,ht,hfresh,hlen⟩ := ih (by omega)
      let i : MedianIndex m := ⟨n,by omega⟩
      obtain ⟨local',hbatch⟩ := hlocal i
      have hsi : prefixState n final i = batchInitial := by simp [prefixState,i]
      have hp : ∀ k : MedianIndex m, k < i → controlLabel (prefixState n final k).1 = none := by
        intro k hk
        have hkn : k.val < n := hk
        simpa only [prefixState,ite_eq_left hkn] using hstop k
      obtain ⟨u,hu,hother⟩ := lift_batch_consumes i hbatch (prefixState n final) t hsi
        (hfresh i (by rfl)) hp
      have hupdate : Function.update (prefixState n final) i (final i) = prefixState (n+1) final := by
        funext k
        by_cases hki : k = i
        · subst k
          simp [prefixState,i]
        · have hval : k.val ≠ n := by intro he; exact hki (Fin.ext he)
          have he : k.val < n+1 ↔ k.val < n := by omega
          simp only [Function.update_of_ne hki,prefixState,he]
      rw [hupdate] at hu
      refine ⟨xs++words i,u,ht.append hu, ?_, ?_⟩
      · intro k hk j
        have hki : k ≠ i := by intro he; subst k; change n+1 ≤ n at hk; omega
        rw [hother k hki j]
        exact hfresh k (by omega) j
      · have hfilter : Finset.univ.filter (fun k : MedianIndex m => k.val < n+1) =
            insert i (Finset.univ.filter (fun k : MedianIndex m => k.val < n)) := by
          ext k
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
          constructor
          · intro hk
            by_cases he : k.val = n
            · exact Or.inl (Fin.ext he)
            · exact Or.inr (by omega)
          · rintro (hk | hk)
            · subst k; change n < n+1; omega
            · omega
        have hi : i ∉ Finset.univ.filter (fun k : MedianIndex m => k.val < n) := by simp [i]
        rw [List.length_append,hlen,hfilter,Finset.sum_insert hi]
        exact Nat.add_comm _ _
  obtain ⟨xs,t,ht,_,hlen⟩ := H (2*m+1) le_rfl
  have he : prefixState (2*m+1) final = final := by
    funext i
    exact ite_eq_left i.isLt
  rw [he] at ht
  refine ⟨xs,t,ht,?_⟩
  simpa only [Finset.filter_true_of_mem (fun (i : MedianIndex m) _ => i.isLt)] using hlen

end ThresholdHC.Confidence
