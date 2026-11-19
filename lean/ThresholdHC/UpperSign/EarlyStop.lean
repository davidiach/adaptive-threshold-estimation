import ThresholdHC.UpperSign.SignChange
import ThresholdHC.UpperDisagreement.ErrorSum

/-! Consecutive classifiers on the tape, below their caps.

If the cap-`2^L` classifier runs to its cap, the cap-`2^(L+1)` classifier
agrees with it unless the majority votes after `2^L` and `2^(L+1)` flips differ
(`decision_ne_imp`). The first classifier stops early only if some check sees
the running mean far from one half. For a coin with gap `d`, that happens in
the direction of the drift with probability at most `driftBound`, and against
it with probability at most the early-stopping error terms of `stopError`
(`early_positive`, `early_negative`). With the sign-change bound of
`SignChange`, consecutive classifiers past the first level disagree with
probability at most one half plus that early-stop bound (`disagree_tape_le`). -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

section EarlyStop
open Real Uniform713

/-- If the cap-`2^L` classifier runs to its cap, the cap-`2^(L+1)` classifier agrees
with it unless the votes at the two caps differ. -/
theorem decision_ne_imp (m : ℕ → ℝ) (L : ℕ)
    (hno : ∀ k < L, |m k - 1/2| ≤ Tier2.Model.threshold1 (cap k) (cap L))
    (hne : Tier2.Model.decision m (L + 1) ≠ Tier2.Model.decision m L) :
    (1/2 < m L ∧ ¬ 1/2 < m (L + 1)) ∨ (¬ 1/2 < m L ∧ 1/2 < m (L + 1)) := by
  have hS : Tier2.Model.stopLevel m L = L := by
    unfold Tier2.Model.stopLevel
    rw [firstStop_eq_iff]
    exact ⟨Or.inl le_rfl, fun j hj => ⟨hj, hno j hj⟩⟩
  have hS1 : L ≤ Tier2.Model.stopLevel m (L + 1) := by
    have := Tier2.Model.stopLevel_mono m (Nat.le_succ L)
    rwa [hS] at this
  have hS2 : Tier2.Model.stopLevel m (L + 1) ≤ L + 1 := Tier2.Model.stopLevel_le m (L + 1)
  have hdL : Tier2.Model.decision m L = if 1/2 < m L then 1 else 0 := by
    unfold Tier2.Model.decision firstDecision
    rw [show firstStop (fun k L => Tier2.Model.threshold1 (cap k) (cap L)) m L = L from hS]
  rcases Nat.eq_or_lt_of_le hS1 with h | h
  · exfalso
    apply hne
    rw [hdL]
    unfold Tier2.Model.decision firstDecision
    rw [show firstStop (fun k L => Tier2.Model.threshold1 (cap k) (cap L)) m (L + 1) = L from h.symm]
  · have h' : Tier2.Model.stopLevel m (L + 1) = L + 1 := by omega
    have hdL1 : Tier2.Model.decision m (L + 1) = if 1/2 < m (L + 1) then 1 else 0 := by
      unfold Tier2.Model.decision firstDecision
      rw [show firstStop (fun k L => Tier2.Model.threshold1 (cap k) (cap L)) m (L + 1) = L + 1
        from h']
    rw [hdL, hdL1] at hne
    by_cases h1 : 1/2 < m L <;> by_cases h2 : 1/2 < m (L + 1)
    · exact (hne (by rw [ite_eq_left h2, ite_eq_left h1])).elim
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact (hne (by rw [ite_eq_right h2, ite_eq_right h1])).elim

/-- The bound on stopping early in the direction of the drift at check `k` of the
cap-`2^L` classifier, on a coin with gap `d`. -/
def driftBound (L k : ℕ) (d : ℝ) : ℝ :=
  if d ≤ Tier2.Model.threshold1 (cap k) (cap L) then
    Real.exp (-2 * cap k * (Tier2.Model.threshold1 (cap k) (cap L) - d) ^ 2) else 1

/-- The early-stop bound of the cap-`2^L` classifier: the drift terms plus the
error terms of `stopError`. -/
def earlyBound (L : ℕ) (d : ℝ) : ℝ :=
  ∑ k ∈ range L, driftBound L k d + UpperDisagreement.stopError L d

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem early_positive (L : ℕ) {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1 / 2 + d)) :
    μ.real {ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) < |m k ω - 1/2|} ≤
      earlyBound L d := by
  set t : ℕ → ℝ := fun k => Tier2.Model.threshold1 (cap k) (cap L) with htdef
  have hsub : {ω | ∃ k < L, t k < |m k ω - 1/2|} ⊆
      ⋃ k ∈ range L, ({ω | t k - d ≤ m k ω - (1/2 + d)} ∪ {ω | t k + d ≤ (1/2 + d) - m k ω}) := by
    intro ω ⟨k, hk, hlt⟩
    refine Set.mem_iUnion₂.2 ⟨k, mem_range.2 hk, ?_⟩
    rcases lt_abs.1 hlt with h | h
    · left; simp only [Set.mem_ofPred_eq]; linarith
    · right; simp only [Set.mem_ofPred_eq]; linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  unfold earlyBound UpperDisagreement.stopError
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  refine (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
  · unfold driftBound
    split_ifs with h
    · exact ht.upper k _ (by simp only [htdef] at h ⊢; linarith)
    · exact measureReal_le_one
  · have := ht.lower k (t k + d) (by have := Tier2.Model.threshold1_nonneg (cap k) (cap L); simp only [htdef]; linarith)
    simpa [htdef, add_comm] using this

theorem early_negative (L : ℕ) {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1 / 2 - d)) :
    μ.real {ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) < |m k ω - 1/2|} ≤
      earlyBound L d := by
  set t : ℕ → ℝ := fun k => Tier2.Model.threshold1 (cap k) (cap L) with htdef
  have hsub : {ω | ∃ k < L, t k < |m k ω - 1/2|} ⊆
      ⋃ k ∈ range L, ({ω | t k - d ≤ (1/2 - d) - m k ω} ∪ {ω | t k + d ≤ m k ω - (1/2 - d)}) := by
    intro ω ⟨k, hk, hlt⟩
    refine Set.mem_iUnion₂.2 ⟨k, mem_range.2 hk, ?_⟩
    rcases lt_abs.1 hlt with h | h
    · right; simp only [Set.mem_ofPred_eq]; linarith
    · left; simp only [Set.mem_ofPred_eq]; linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  unfold earlyBound UpperDisagreement.stopError
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  refine (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
  · unfold driftBound
    split_ifs with h
    · exact ht.lower k _ (by simp only [htdef] at h ⊢; linarith)
    · exact measureReal_le_one
  · have := ht.upper k (t k + d) (by have := Tier2.Model.threshold1_nonneg (cap k) (cap L); simp only [htdef]; linarith)
    simpa [htdef, add_comm] using this

end EarlyStop

section Tape
open Real Uniform713

theorem sum_bit_eq (s n : ℕ) (ω : ℕ → Bool) :
    ∑ i ∈ range n, observations (s + i) ω = (successes s n ω : ℝ) := by
  unfold successes observations bit
  push_cast
  rfl

theorem dyadicMean_eq (L : ℕ) (ω : ℕ → Bool) :
    dyadicMean observations L ω = (successes 0 (2 ^ L) ω : ℝ) / 2 ^ L := by
  unfold dyadicMean prefixMean
  rw [← sum_bit_eq 0 (2 ^ L) ω]
  simp

theorem dyadicMean_succ_eq (L : ℕ) (ω : ℕ → Bool) :
    dyadicMean observations (L + 1) ω =
      ((successes 0 (2 ^ L) ω : ℝ) + (successes (2 ^ L) (2 ^ L) ω : ℝ)) / 2 ^ (L + 1) := by
  unfold dyadicMean prefixMean
  rw [← sum_bit_eq 0 (2 ^ L) ω, ← sum_bit_eq (2 ^ L) (2 ^ L) ω,
    show 2 ^ (L + 1) = 2 ^ L + 2 ^ L by ring, sum_range_add]
  simp only [zero_add]
  push_cast
  rw [pow_succ]
  ring

/-- On the tape, consecutive classifiers past the first level disagree with
probability at most one half plus the early-stop bound of the smaller one. -/
theorem disagree_tape_le (L : ℕ) (hL : 1 ≤ L) (p : unitInterval) {d : ℝ}
    (hearly : (tapeMeasure p).real {ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) <
      |dyadicMean observations k ω - 1/2|} ≤ earlyBound L d) :
    (tapeMeasure p).real {ω | Tier2.Model.decision (fun k => dyadicMean observations k ω) (L + 1) ≠
      Tier2.Model.decision (fun k => dyadicMean observations k ω) L} ≤ 1 / 2 + earlyBound L d := by
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ L = 2 * M := ⟨2 ^ (L - 1), by
    rw [← pow_succ']; congr 1; omega⟩
  set μ := tapeMeasure p
  have hsub : {ω | Tier2.Model.decision (fun k => dyadicMean observations k ω) (L + 1) ≠
      Tier2.Model.decision (fun k => dyadicMean observations k ω) L} ⊆
      {ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) <
        |dyadicMean observations k ω - 1/2|} ∪
      {ω | (M < successes 0 (2 * M) ω ∧ successes (2 * M) (2 * M) ω < M) ∨
        (successes 0 (2 * M) ω ≤ M ∧ M < successes (2 * M) (2 * M) ω)} := by
    intro ω hω
    by_cases hno : ∀ k < L, |dyadicMean observations k ω - 1/2| ≤
        Tier2.Model.threshold1 (cap k) (cap L)
    · right
      have hs := decision_ne_imp (fun k => dyadicMean observations k ω) L hno hω
      simp only [Set.mem_ofPred_eq]
      have hMr : (2 : ℝ) ^ L = 2 * (M : ℝ) := by exact_mod_cast hM
      have h2M : (0 : ℝ) < 2 * M := by rw [← hMr]; positivity
      have hpow : (2 : ℝ) ^ (L + 1) = 2 * (2 * M) := by rw [pow_succ, hMr]; ring
      rw [dyadicMean_eq, dyadicMean_succ_eq, hM, hpow] at hs
      rw [hMr] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [lt_div_iff₀ h2M] at h1
        rw [lt_div_iff₀ (by positivity)] at h2
        constructor
        · exact_mod_cast (show (M : ℝ) < successes 0 (2 * M) ω by linarith)
        · have : (successes 0 (2 * M) ω : ℝ) + successes (2 * M) (2 * M) ω ≤ 2 * M := by
            push Not at h2
            linarith
          have : successes 0 (2 * M) ω + successes (2 * M) (2 * M) ω ≤ 2 * M := by
            exact_mod_cast this
          have : M < successes 0 (2 * M) ω := by exact_mod_cast (show (M : ℝ) < successes 0 (2 * M) ω by linarith)
          omega
      · right
        rw [lt_div_iff₀ h2M] at h1
        rw [lt_div_iff₀ (by positivity)] at h2
        have ha : successes 0 (2 * M) ω ≤ M := by
          have : (successes 0 (2 * M) ω : ℝ) ≤ M := by push Not at h1; linarith
          exact_mod_cast this
        have hb : 2 * M < successes 0 (2 * M) ω + successes (2 * M) (2 * M) ω := by
          have : (2 * M : ℝ) < successes 0 (2 * M) ω + successes (2 * M) (2 * M) ω := by linarith
          exact_mod_cast this
        exact ⟨ha, by omega⟩
    · left
      push Not at hno
      exact hno
  calc
    _ ≤ μ.real ({ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) <
          |dyadicMean observations k ω - 1/2|} ∪
        {ω | (M < successes 0 (2 * M) ω ∧ successes (2 * M) (2 * M) ω < M) ∨
          (successes 0 (2 * M) ω ≤ M ∧ M < successes (2 * M) (2 * M) ω)}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ earlyBound L d + 1 / 2 := add_le_add hearly (count_signChange_le M p)
    _ = _ := by ring

end Tape

end ThresholdHC.UpperSign
