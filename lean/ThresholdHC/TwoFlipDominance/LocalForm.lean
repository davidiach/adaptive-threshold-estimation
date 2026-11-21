import ThresholdHC.TwoFlipDominance.Specification

/-! The combinatorial core of the dominance step (`feedback.tex`, dominance
paragraph). For a local design at one seed with the first coin `c`, let `S` be
the set of other coins whose rule asks for a flip before any answer. If the
policy revisits `c` after some answer and stops after two flips, `S` is empty.
If `S` is not empty, both branches continue on coins other than `c`. If `S` is
empty, each branch either stops or revisits `c`. Either way the seed is in the
normal form `NoninteractiveCapTwo`. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance

theorem ownBits_nil (pol : List Bool → Option ℕ) (c : ℕ) : ownBits pol c [] = [] := by
  simp [ownBits]

theorem ownBits_one (pol : List Bool → Option ℕ) (c : ℕ) (b : Bool) :
    ownBits pol c [b] = if pol [] = some c then [b] else [] := by
  by_cases h : pol [] = some c <;> simp [ownBits, h]

theorem ownBits_two (pol : List Bool → Option ℕ) (c : ℕ) (b b' : Bool) :
    ownBits pol c [b, b'] = (if pol [] = some c then [b] else []) ++
      (if pol [b] = some c then [b'] else []) := by
  by_cases h : pol [] = some c <;> by_cases h' : pol [b] = some c <;>
    simp [ownBits, h, h', List.range_succ]

/-- The class condition at one seed, for a policy `pol` and continuation rules `cont`. -/
def LocalAt (pol : List Bool → Option ℕ) (cont : ℕ → List Bool → Bool) : Prop :=
  ∀ xs : List Bool, (pol xs = none ↔ ∀ c, cont c (ownBits pol c xs) = false) ∧
    ∀ c, pol xs = some c → cont c (ownBits pol c xs) = true

/-- The normal form at one seed. -/
def NormalAt (pol : List Bool → Option ℕ) : Prop :=
  ∀ c : ℕ, pol [] = some c →
    (∀ b : Bool, pol [b] = none ∨ pol [b] = some c) ∨
    ((∀ b : Bool, pol [b] ≠ some c) ∧ (pol [false]).isSome = (pol [true]).isSome)

/-- The policy stops after two flips. -/
def StopsAtTwo (pol : List Bool → Option ℕ) : Prop :=
  ∀ b b' : Bool, pol [] ≠ none → pol [b] ≠ none → pol [b, b'] = none

theorem other_off (pol : List Bool → Option ℕ) (c d : ℕ) (hc : pol [] = some c) (hdc : d ≠ c)
    (b : Bool) : ownBits pol d [b] = [] := by
  rw [ownBits_one, hc]
  simp [Ne.symm hdc]

/-- The dominance step at one seed. -/
theorem local_normal_form (pol : List Bool → Option ℕ) (cont : ℕ → List Bool → Bool)
    (hloc : LocalAt pol cont) (hstop : StopsAtTwo pol) : NormalAt pol := by
  intro c hc
  by_cases hS : ∃ d, d ≠ c ∧ cont d [] = true
  · obtain ⟨d, hdc, hd⟩ := hS
    have hactive (b : Bool) : pol [b] ≠ none := by
      intro hb
      have h := ((hloc [b]).1.mp hb) d
      rw [other_off pol c d hc hdc b] at h
      rw [h] at hd
      exact Bool.false_ne_true hd
    have hfresh (b : Bool) : pol [b] ≠ some c := by
      intro hb
      have h2 := hstop b false (by rw [hc]; exact Option.some_ne_none c) (by rw [hb]; exact Option.some_ne_none c)
      have h := ((hloc [b, false]).1.mp h2) d
      have e : ownBits pol d [b, false] = [] := by
        rw [ownBits_two, hc, hb]
        simp [Ne.symm hdc]
      rw [e] at h
      rw [h] at hd
      exact Bool.false_ne_true hd
    refine Or.inr ⟨hfresh, ?_⟩
    rw [Option.isSome_iff_ne_none.mpr (hactive false), Option.isSome_iff_ne_none.mpr (hactive true)]
  · refine Or.inl fun b => ?_
    cases hb : pol [b] with
    | none => exact Or.inl rfl
    | some e =>
      by_cases he : e = c
      · subst he
        exact Or.inr rfl
      · exfalso
        have h := (hloc [b]).2 e hb
        rw [other_off pol c e hc he b] at h
        exact hS ⟨e, he, h⟩

/-- For a policy that stops at length two only the first two answers are charged. -/
theorem ownBits_stopAt_long (p : List Bool → ℕ) (c : ℕ) (a b : Bool) (t : List Bool) :
    ownBits (ThresholdHC.HardBudget.stopAt 2 p) c (a :: b :: t) =
      ownBits (ThresholdHC.HardBudget.stopAt 2 p) c [a, b] := by
  have hoff : ((List.range t.length).map (fun k => k + 1 + 1)).filter
      (fun k => decide (ThresholdHC.HardBudget.stopAt 2 p ((a :: b :: t).take k) = some c)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro k hk
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
    simp [ThresholdHC.HardBudget.stopAt]
  rw [ownBits_two]
  unfold ownBits
  simp only [List.length_cons]
  rw [List.range_succ_eq_map, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [List.filter_cons, List.filter_cons]
  have e : (List.map (Nat.succ ∘ Nat.succ) (List.range t.length)) =
      (List.range t.length).map (fun k => k + 1 + 1) := rfl
  rw [e, hoff]
  by_cases h0 : ThresholdHC.HardBudget.stopAt 2 p [] = some c <;>
    by_cases h1 : ThresholdHC.HardBudget.stopAt 2 p [a] = some c <;> simp [h0, h1]

end ThresholdHC.TwoFlipDominance
