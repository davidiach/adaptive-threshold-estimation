import ThresholdHC.BlindUpper.FiniteProcedure

/-! A pointwise observable finite search over prefix predicates. The cap is
part of the procedure; no termination assumption about the searched bank is
required. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

def boundedFirst (hit : ℕ → Prop) (M : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ n, n ≤ M ∧ (hit n ∨ n = M) from ⟨M, le_rfl, Or.inr rfl⟩)

theorem boundedFirst_spec (hit : ℕ → Prop) (M : ℕ) :
    boundedFirst hit M ≤ M ∧ (hit (boundedFirst hit M) ∨ boundedFirst hit M = M) := by
  classical
  exact Nat.find_spec (show ∃ n, n ≤ M ∧ (hit n ∨ n = M) from ⟨M, le_rfl, Or.inr rfl⟩)

theorem boundedFirst_before (hit : ℕ → Prop) (M k : ℕ) (hk : k < boundedFirst hit M) : ¬ hit k := by
  classical
  intro h
  have hmin := Nat.find_min (show ∃ n, n ≤ M ∧ (hit n ∨ n=M) from ⟨M,le_rfl,Or.inr rfl⟩) hk
  exact hmin ⟨hk.le.trans (boundedFirst_spec hit M).1, Or.inl h⟩

theorem boundedFirst_le_of_hit (hit : ℕ → Prop) (M n : ℕ) (hn : hit n) : boundedFirst hit M ≤ n := by
  classical
  by_cases h : n ≤ M
  · exact Nat.find_min' (show ∃ k, k ≤ M ∧ (hit k ∨ k = M) from ⟨M, le_rfl, Or.inr rfl⟩) ⟨h, Or.inl hn⟩
  · exact (boundedFirst_spec hit M).1.trans (le_of_not_ge h)

theorem boundedFirst_congr_until (hit hit' : ℕ → Prop) (M : ℕ)
    (he : ∀ n ≤ boundedFirst hit M, hit n ↔ hit' n) : boundedFirst hit M = boundedFirst hit' M := by
  classical
  have hle : boundedFirst hit' M ≤ boundedFirst hit M := by
    apply Nat.find_min' (show ∃ k, k ≤ M ∧ (hit' k ∨ k = M) from ⟨M, le_rfl, Or.inr rfl⟩)
    refine ⟨(boundedFirst_spec hit M).1, ?_⟩
    rcases (boundedFirst_spec hit M).2 with h | h
    · exact Or.inl ((he _ le_rfl).mp h)
    · exact Or.inr h
  apply le_antisymm _ hle
  by_contra hn
  have hlt := lt_of_not_ge hn
  rcases (boundedFirst_spec hit' M).2 with h | h
  · exact boundedFirst_before hit M _ hlt ((he _ hle).mpr h)
  · have hb := (boundedFirst_spec hit M).1
    omega

def prefixSearchCost (hit : (n : ℕ) → (Fin n → Bool) → Prop) (M : ℕ) (ω : ℕ → Bool) : ℕ :=
  boundedFirst (fun n => hit n (tapePrefix n ω)) M

theorem prefixSearchCost_le (hit : (n : ℕ) → (Fin n → Bool) → Prop) (M : ℕ) (ω : ℕ → Bool) :
    prefixSearchCost hit M ω ≤ M := (boundedFirst_spec _ M).1

theorem prefixSearchCost_ext (hit : (n : ℕ) → (Fin n → Bool) → Prop) (M : ℕ)
    (ω ω' : ℕ → Bool)
    (he : tapePrefix (prefixSearchCost hit M ω) ω = tapePrefix (prefixSearchCost hit M ω) ω') :
    prefixSearchCost hit M ω' = prefixSearchCost hit M ω := by
  apply (boundedFirst_congr_until _ _ M _).symm
  intro n hn
  rw [prefix_eq_restrict he hn]

theorem measurable_prefixSearchCost (hit : (n : ℕ) → (Fin n → Bool) → Prop) (M : ℕ) :
    Measurable (prefixSearchCost hit M) := by
  have he : prefixSearchCost hit M =
      (fun w => prefixSearchCost hit M (completePrefix M w)) ∘ tapePrefix M := by
    funext ω
    exact (prefixSearchCost_ext hit M ω (completePrefix M (tapePrefix M ω))
      (prefix_eq_restrict (tapePrefix_completePrefix M _).symm (prefixSearchCost_le hit M ω))).symm
  rw [he]
  exact (measurable_of_countable _).comp (measurable_prefix M)

def prefixSearchValue {E : Type*} (hit : (n : ℕ) → (Fin n → Bool) → Prop)
    (value : (n : ℕ) → (Fin n → Bool) → E) (M : ℕ) (ω : ℕ → Bool) : E :=
  value (prefixSearchCost hit M ω) (tapePrefix (prefixSearchCost hit M ω) ω)

theorem prefixSearchValue_ext {E : Type*} (hit : (n : ℕ) → (Fin n → Bool) → Prop)
    (value : (n : ℕ) → (Fin n → Bool) → E) (M : ℕ) (ω ω' : ℕ → Bool)
    (he : tapePrefix (prefixSearchCost hit M ω) ω = tapePrefix (prefixSearchCost hit M ω) ω') :
    prefixSearchValue hit value M ω' = prefixSearchValue hit value M ω := by
  unfold prefixSearchValue
  rw [prefixSearchCost_ext hit M ω ω' he, he]

theorem measurable_prefixSearchValue {E : Type*} [MeasurableSpace E]
    (hit : (n : ℕ) → (Fin n → Bool) → Prop) (value : (n : ℕ) → (Fin n → Bool) → E) (M : ℕ) :
    Measurable (prefixSearchValue hit value M) := by
  have he : prefixSearchValue hit value M =
      (fun w => prefixSearchValue hit value M (completePrefix M w)) ∘ tapePrefix M := by
    funext ω
    exact (prefixSearchValue_ext hit value M ω (completePrefix M (tapePrefix M ω))
      (prefix_eq_restrict (tapePrefix_completePrefix M _).symm (prefixSearchCost_le hit M ω))).symm
  rw [he]
  exact (measurable_of_countable _).comp (measurable_prefix M)

def prefixSearchProcedure {E : Type} [MeasurableSpace E]
    (hit : (n : ℕ) → (Fin n → Bool) → Prop) (value : (n : ℕ) → (Fin n → Bool) → E) (M : ℕ) :
    StoppedProcedure Unit E :=
  finiteStoppedProcedure (fun z => prefixSearchCost hit M z.2)
    (fun z => prefixSearchValue hit value M z.2)
    ((measurable_prefixSearchCost hit M).comp measurable_snd)
    ((measurable_prefixSearchValue hit value M).comp measurable_snd)
    (fun _ ω ω' he => ⟨prefixSearchCost_ext hit M ω ω' he, prefixSearchValue_ext hit value M ω ω' he⟩)

end ThresholdHC.EntropyTailUpper
