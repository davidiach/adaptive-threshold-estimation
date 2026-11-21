import ThresholdHC.RepeatedCheck.Row
import ThresholdHC.Proofs.Tier2.ClassifierProbability

/-! Exact path counting for display (29) of
`research/2026-10-30-confidence-transfer/ANYTIME.md`.

The event that the check `(4H_n - n)² > 12n` fires at some `n ≤ N` depends on
the first `N` flips only. Its complement is the survival event of the word of
the first `N` flips, whose indicator is `aliveWeight`. Summing the iid
Bernoulli(1/4) word probabilities of surviving words of length `n` with `k`
heads gives `survivalMass n k`, which satisfies the survivor recursion
(a tail has probability `3/4`, a head `1/4`), so it equals
`survivor n k / 4^n`. Hence the repeated-check probability is
`1 - (survivorRow N).sum / 4^N` (`repeatedEvent_real`). -/

noncomputable section
open MeasureTheory ProbabilityTheory
open ThresholdHC.Tier2

namespace ThresholdHC.RepeatedCheck

/-- Number of heads of a finite word. -/
def wordCount {n : ℕ} (w : Fin n → Bool) : ℕ := ∑ i, if w i = true then 1 else 0

/-- Number of heads among the first `m` letters of a finite word. -/
def prefixCount {n : ℕ} (w : Fin n → Bool) (m : ℕ) : ℕ :=
  ∑ i : Fin n, if i.val < m ∧ w i = true then 1 else 0

/-- Survival indicator of a word of length `n`: no crossing at the lengths
`1, …, n`. -/
def aliveWeight {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∏ j : Fin n, if crossNat (j.val + 1) (prefixCount w (j.val + 1)) = true then 0 else 1

/-- Probability under iid Bernoulli(1/4) flips of the surviving words of
length `n` with `k` heads. -/
def survivalMass (n k : ℕ) : ℝ :=
  ∑ w : Fin n → Bool, if wordCount w = k then aliveWeight w * streamProb (1/4 : ℝ) w else 0

/-- The repeated-check event up to horizon `N`. -/
def repeatedEvent (N : ℕ) : Set (ℕ → Bool) :=
  {ω | ∃ n : ℕ, n ≤ N ∧
    12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2}

theorem wordCount_snoc {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    wordCount (Fin.snoc w b : Fin (n + 1) → Bool) = wordCount w + if b = true then 1 else 0 := by
  simp only [wordCount, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem wordCount_le {n : ℕ} (w : Fin n → Bool) : wordCount w ≤ n := by
  unfold wordCount
  calc _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by split <;> omega
    _ = n := by simp

theorem prefixCount_snoc {n : ℕ} (w : Fin n → Bool) (b : Bool) (m : ℕ) :
    prefixCount (Fin.snoc w b : Fin (n + 1) → Bool) m =
      prefixCount w m + if n < m ∧ b = true then 1 else 0 := by
  simp only [prefixCount, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last]

theorem prefixCount_of_le {n : ℕ} (w : Fin n → Bool) (m : ℕ) (h : n ≤ m) :
    prefixCount w m = wordCount w := by
  unfold prefixCount wordCount
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < m := lt_of_lt_of_le i.isLt h
  simp [hi]

theorem aliveWeight_snoc {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    aliveWeight (Fin.snoc w b : Fin (n + 1) → Bool) =
      aliveWeight w *
        (if crossNat (n + 1) (wordCount w + if b = true then 1 else 0) = true then 0 else 1) := by
  unfold aliveWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    have hj : ¬(n < j.val + 1 ∧ b = true) := fun h => by have := j.isLt; omega
    simp only [Fin.val_castSucc, prefixCount_snoc, hj, ite_false, add_zero]
  · simp only [Fin.val_last, prefixCount_snoc, prefixCount_of_le w (n + 1) (by omega)]
    by_cases hb : b = true
    · simp [hb]
    · simp [hb]

theorem streamProb_snoc {n : ℕ} (p : ℝ) (w : Fin n → Bool) (b : Bool) :
    streamProb p (Fin.snoc w b : Fin (n + 1) → Bool) =
      streamProb p w * (if b = true then p else 1 - p) := by
  simp only [streamProb, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem survivalMass_succ (n k : ℕ) :
    survivalMass (n + 1) k = (if crossNat (n + 1) k = true then 0 else 1) *
      (survivalMass n k * (3/4) + if k = 0 then 0 else survivalMass n (k - 1) * (1/4)) := by
  have he := (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
    (fun w => if wordCount w = k then aliveWeight w * streamProb (1/4 : ℝ) w else 0)
  unfold survivalMass
  rw [← he, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.snocEquiv_apply, wordCount_snoc, aliveWeight_snoc, streamProb_snoc, ite_true,
    Bool.false_eq_true, ite_false, add_zero]
  have hfalse : (∑ w : Fin n → Bool, if wordCount w = k then
      aliveWeight w * (if crossNat (n + 1) (wordCount w) = true then 0 else 1) *
        (streamProb (1/4 : ℝ) w * (1 - 1/4)) else 0) =
      (if crossNat (n + 1) k = true then 0 else 1) * ((∑ w : Fin n → Bool,
        if wordCount w = k then aliveWeight w * streamProb (1/4 : ℝ) w else 0) * (3/4)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : wordCount w = k
    · rw [ite_eq_left hw, ite_eq_left hw, hw]
      ring
    · rw [ite_eq_right hw, ite_eq_right hw]
      ring
  have htrue : (∑ w : Fin n → Bool, if wordCount w + 1 = k then
      aliveWeight w * (if crossNat (n + 1) (wordCount w + 1) = true then 0 else 1) *
        (streamProb (1/4 : ℝ) w * (1/4)) else 0) =
      (if crossNat (n + 1) k = true then 0 else 1) * (if k = 0 then 0 else (∑ w : Fin n → Bool,
        if wordCount w = k - 1 then aliveWeight w * streamProb (1/4 : ℝ) w else 0) * (1/4)) := by
    by_cases hk : k = 0
    · rw [ite_eq_left hk, mul_zero]
      apply Finset.sum_eq_zero
      intro w _
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_right hk, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : wordCount w + 1 = k
      · have hw' : wordCount w = k - 1 := by omega
        rw [ite_eq_left hw, ite_eq_left hw', hw]
        ring
      · have hw' : ¬wordCount w = k - 1 := by omega
        rw [ite_eq_right hw, ite_eq_right hw']
        ring
  rw [htrue, hfalse]
  ring

theorem survivalMass_zero (k : ℕ) : survivalMass 0 k = if k = 0 then 1 else 0 := by
  unfold survivalMass
  rw [Fintype.sum_unique]
  simp only [wordCount, aliveWeight, streamProb, Finset.univ_eq_empty, Finset.sum_empty,
    Finset.prod_empty, mul_one]
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk, Ne.symm hk]

/-- The surviving mass of length-`n` words with `k` heads is `survivor n k / 4^n`. -/
theorem survivalMass_eq (n k : ℕ) : survivalMass n k = (survivor n k : ℝ) / 4 ^ n := by
  induction n generalizing k with
  | zero =>
    rw [survivalMass_zero, survivor_zero]
    split_ifs <;> simp
  | succ n ih =>
    rw [survivalMass_succ, ih, ih, survivor_succ]
    cases hc : crossNat (n + 1) k
    · by_cases hk : k = 0
      · simp only [hk, ite_true, Bool.false_eq_true, ite_false, Bool.cond_false, add_zero, one_mul]
        push_cast
        rw [pow_succ]
        field_simp
      · simp only [hk, ite_false, Bool.false_eq_true, Bool.cond_false, one_mul]
        push_cast
        rw [pow_succ]
        field_simp
    · simp

theorem survivorRow_sum_real (n : ℕ) :
    ((survivorRow n).sum : ℝ) = ∑ k ∈ Finset.range (n + 1), (survivor n k : ℝ) := by
  rw [survivorRow_sum]
  push_cast
  rfl

/-- The total mass of the surviving words of length `n`. -/
theorem survival_total (n : ℕ) :
    ∑ w : Fin n → Bool, streamProb (1/4 : ℝ) w * aliveWeight w =
      ((survivorRow n).sum : ℝ) / 4 ^ n := by
  have hfib : ∑ w : Fin n → Bool, streamProb (1/4 : ℝ) w * aliveWeight w =
      ∑ k ∈ Finset.range (n + 1), survivalMass n k := by
    unfold survivalMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_of_le (wordCount_le w)))]
    ring
  rw [hfib, survivorRow_sum_real, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => survivalMass_eq n k

theorem prefixCount_tape (N m : ℕ) (hm : m ≤ N) (ω : ℕ → Bool) :
    prefixCount (tapePrefix N ω) m = ((Finset.range m).filter (fun t => ω t = true)).card := by
  unfold prefixCount tapePrefix
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m ∧ ω i = true then 1 else 0) N,
    ← Finset.card_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h1, h2⟩

theorem aliveWeight_tape_of_mem (N : ℕ) (ω : ℕ → Bool) (h : ω ∈ repeatedEvent N) :
    aliveWeight (tapePrefix N ω) = 0 := by
  obtain ⟨n, hn, hcross⟩ := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hcross
  let j : Fin N := ⟨n - 1, by omega⟩
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  have hj : j.val + 1 = n := by
    change n - 1 + 1 = n
    omega
  rw [hj, prefixCount_tape N n hn ω]
  have hc : crossNat n ((Finset.range n).filter (fun t => ω t = true)).card = true :=
    (crossNat_iff _ _).mpr hcross
  rw [ite_eq_left hc]

theorem aliveWeight_tape_of_notMem (N : ℕ) (ω : ℕ → Bool) (h : ω ∉ repeatedEvent N) :
    aliveWeight (tapePrefix N ω) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  have hjN : j.val + 1 ≤ N := j.isLt
  rw [prefixCount_tape N (j.val + 1) hjN ω]
  have hc : crossNat (j.val + 1)
      ((Finset.range (j.val + 1)).filter (fun t => ω t = true)).card ≠ true := by
    intro hc
    exact h ⟨j.val + 1, hjN, (crossNat_iff _ _).mp hc⟩
  rw [ite_eq_right hc]

theorem indicator_repeatedEvent_compl (N : ℕ) (ω : ℕ → Bool) :
    (repeatedEvent N)ᶜ.indicator 1 ω = aliveWeight (tapePrefix N ω) := by
  by_cases h : ω ∈ repeatedEvent N
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h), aliveWeight_tape_of_mem N ω h]
  · rw [Set.indicator_of_mem h, aliveWeight_tape_of_notMem N ω h]
    rfl

theorem repeatedEvent_eq_preimage (N : ℕ) :
    repeatedEvent N = (fun ω => aliveWeight (tapePrefix N ω)) ⁻¹' {0} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · exact aliveWeight_tape_of_mem N ω
  · intro h0
    by_contra h
    rw [aliveWeight_tape_of_notMem N ω h] at h0
    exact one_ne_zero h0

theorem measurableSet_repeatedEvent (N : ℕ) : MeasurableSet (repeatedEvent N) := by
  have hm : Measurable (fun ω => aliveWeight (tapePrefix N ω)) :=
    (measurable_of_countable (fun w : Fin N → Bool => aliveWeight w)).comp (measurable_prefix N)
  rw [repeatedEvent_eq_preimage]
  exact hm (measurableSet_singleton 0)

/-- The exact repeated-check probability at `θ = 1/4`. -/
theorem repeatedEvent_real (θ : unitInterval) (hθ : (θ : ℝ) = 1/4) (N : ℕ) :
    (tapeMeasure θ).real (repeatedEvent N) = 1 - ((survivorRow N).sum : ℝ) / 4 ^ N := by
  have hE := measurableSet_repeatedEvent N
  have hc : (tapeMeasure θ).real (repeatedEvent N)ᶜ =
      ∑ x : Fin N → Bool, streamProb (θ : ℝ) x * aliveWeight x := by
    rw [← integral_indicator_one hE.compl, ← integral_prefix]
    congr 1
    funext ω
    exact indicator_repeatedEvent_compl N ω
  rw [probReal_compl_eq_one_sub hE, hθ, survival_total] at hc
  linarith

end ThresholdHC.RepeatedCheck
