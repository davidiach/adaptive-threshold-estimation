import ThresholdHC.StoppingProgram.WordFlow

/-! Ordered-prefix survival weights are exact indicators for the observable
table call. These are pointwise identities on the original tape space. -/

noncomputable section
open scoped BigOperators Classical
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailUpper

theorem shortWord_tapePrefix (ω : ℕ → Bool) (m n : ℕ) (hm : m ≤ n) :
    shortWord (tapePrefix n ω) m hm = tapePrefix m ω := by
  funext i
  rfl

theorem countDecision_binary {N : ℕ} (b : CountState N → Bool) (n k : ℕ) :
    countDecision b n k = 0 ∨ countDecision b n k = 1 := by
  unfold countDecision arrayAt
  split_ifs <;> simp

theorem tableCost_ge_iff {N : ℕ} (b : CountState N → Bool) (ω : ℕ → Bool) (n : ℕ) (hn : n ≤ N) :
    n ≤ tableCost b ω ↔ ∀ j, j < n → ¬tableHit b j (tapePrefix j ω) := by
  constructor
  · intro h j hj
    exact boundedFirst_before _ N j (lt_of_lt_of_le hj h)
  · intro h
    by_contra hc
    have hlt : tableCost b ω < n := lt_of_not_ge hc
    have hs := (boundedFirst_spec (fun j => tableHit b j (tapePrefix j ω)) N).2
    change tableHit b (tableCost b ω) (tapePrefix (tableCost b ω) ω) ∨ tableCost b ω = N at hs
    rcases hs with hs | hs
    · exact h _ hlt hs
    · omega

theorem countDecision_complement_hit {N : ℕ} (b : CountState N → Bool) (hb : b (rootState N) = false)
    (ω : ℕ → Bool) (n : ℕ) :
    1-countDecision b n (wordHeads (tapePrefix n ω)) =
      if ¬tableHit b n (tapePrefix n ω) then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    have hh : wordHeads (tapePrefix 0 ω) = 0 := by simp [wordHeads]
    have hc : countDecision b 0 0 = 0 := by
      have h := countDecision_state b (rootState N)
      change countDecision b 0 0 = if b (rootState N) then 1 else 0 at h
      simpa only [hb,Bool.false_eq_true,ite_false] using h
    simp [hh,hc,tableHit]
  · rcases countDecision_binary b n (wordHeads (tapePrefix n ω)) with hc | hc <;>
      simp [hc,tableHit,show 0 < n by omega]

theorem wordArrival_tape_indicator {N : ℕ} (b : CountState N → Bool) (hb : b (rootState N) = false)
    (ω : ℕ → Bool) (n : ℕ) (hn : n ≤ N) :
    wordArrival b (tapePrefix n ω) = if n ≤ tableCost b ω then 1 else 0 := by
  unfold wordArrival
  simp only [shortWord_tapePrefix,countDecision_complement_hit b hb]
  rw [Fintype.prod_boole]
  have he : (∀ j : Fin n, ¬tableHit b j.val (tapePrefix j.val ω)) ↔
      ∀ j, j < n → ¬tableHit b j (tapePrefix j ω) := by
    constructor
    · intro h j hj
      exact h ⟨j,hj⟩
    · intro h j
      exact h j.val j.isLt
  simp only [he,← tableCost_ge_iff b ω n hn]

theorem tableDecision_at_stop {N : ℕ} (_hN : 0 < N) (b : CountState N → Bool)
    (ht : ∀ s : CountState N, s.1.val = N → b s = true) (ω : ℕ → Bool) :
    countDecision b (tableCost b ω) (wordHeads (tapePrefix (tableCost b ω) ω)) = 1 := by
  have hs := (boundedFirst_spec (fun j => tableHit b j (tapePrefix j ω)) N).2
  change tableHit b (tableCost b ω) (tapePrefix (tableCost b ω) ω) ∨ tableCost b ω = N at hs
  rcases hs with hs | hs
  · exact hs.2
  · have he := countDecision_state b (tableStoppedState b ω)
    rw [ht _ hs] at he
    exact he

theorem wordStop_tape_indicator {N : ℕ} (hN : 0 < N) (b : CountState N → Bool)
    (hb : b (rootState N) = false) (ht : ∀ s : CountState N, s.1.val = N → b s = true)
    (ω : ℕ → Bool) (n : ℕ) (hn : n ≤ N) :
    wordArrival b (tapePrefix n ω)*countDecision b n (wordHeads (tapePrefix n ω)) =
      if tableCost b ω = n then 1 else 0 := by
  rw [wordArrival_tape_indicator b hb ω n hn]
  by_cases he : tableCost b ω = n
  · rw [ite_eq_left he,ite_eq_left he.ge]
    have h := tableDecision_at_stop hN b ht ω
    rw [he] at h
    rw [h,mul_one]
  · rw [ite_eq_right he]
    by_cases hn' : n ≤ tableCost b ω
    · rw [ite_eq_left hn',one_mul]
      have hlt : n < tableCost b ω := lt_of_le_of_ne hn' (Ne.symm he)
      have hbefore := boundedFirst_before (fun j => tableHit b j (tapePrefix j ω)) N n hlt
      by_cases hn0 : n = 0
      · subst n
        have h := countDecision_complement_hit b hb ω 0
        simp only [tableHit,lt_self_iff_false,false_and,not_false_eq_true,ite_true] at h
        linarith
      · have hne : countDecision b n (wordHeads (tapePrefix n ω)) ≠ 1 := fun hh => hbefore ⟨by omega,hh⟩
        exact (countDecision_binary b n _).resolve_right hne
    · rw [ite_eq_right hn',zero_mul]

end ThresholdHC.StoppingProgram
