import ThresholdHC.ArbitraryLawAdaptation.TailProbe
import ThresholdHC.HardBudget.Words

/-! The tail probe as a reader of observed flips.

A reader chooses the next coin to flip from the word of flips observed so far.
The probe's reader tests coin `0`, then coin `1`, and so on, each with the
sign-neutral tail test, and it keeps a count of the coins the probe has
completed under its stopping rule: the count freezes once an unresolved coin
is completed or `M` coins are counted. The reader itself keeps buying flips
until its block is full; flips bought after the probe has stopped are charged
and ignored.

The main statement is pathwise. After the reader has bought `t` flips from a
table of coin tapes, the count computed from the observed word equals
`probeCompleted J t M` of that table, the tape-level definition of the probe at
flip budget `t`. Hence the certificate at every cumulative budget is a function
of the observed word, and words at smaller budgets are prefixes of words at
larger ones. No probability enters here. -/

noncomputable section
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.HardBudget ThresholdHC.CriticalEntropy

/-- State of the probe's reader after some observed flips. -/
structure ProbeState where
  /-- Index of the coin being tested. -/
  coin : ℕ
  /-- Index of the next checkpoint of that coin. -/
  level : ℕ
  /-- Flips bought on that coin. -/
  len : ℕ
  /-- Heads among them. -/
  heads : ℕ
  /-- Coins the probe has completed under its stopping rule. -/
  count : ℕ
  /-- The probe has stopped: it will not count another coin. -/
  stopped : Bool

/-- The initial state. A coin cap of zero stops the probe at once. -/
def probeInit (M : ℕ) : ProbeState := ⟨0, 0, 0, 0, 0, decide (M = 0)⟩

/-- The resolving check at checkpoint `k` from the head count `h` of the first
`4^k` flips: `|2h - 4^k| > 2 h_k`. -/
def probeResolved (J k h : ℕ) : Bool :=
  decide (2 * (tailThreshold J k : ℤ) < |2 * (h : ℤ) - ((4 ^ k : ℕ) : ℤ)|)

/-- One observed flip. At a checkpoint the coin's test ends when the check
resolves or the checkpoint is terminal; the reader then moves to the next
coin, and the probe counts the coin unless it has stopped. -/
def probeStep (J M : ℕ) (st : ProbeState) (b : Bool) : ProbeState :=
  if st.len + 1 = 4 ^ st.level then
    if J ≤ st.level ∨ probeResolved J st.level (st.heads + b.toNat) = true then
      { coin := st.coin + 1, level := 0, len := 0, heads := 0,
        count := if st.stopped = true then st.count else st.count + 1,
        stopped := st.stopped || !probeResolved J st.level (st.heads + b.toNat) ||
          decide (M < st.coin + 2) }
    else
      { st with level := st.level + 1, len := st.len + 1, heads := st.heads + b.toNat }
  else
    { st with len := st.len + 1, heads := st.heads + b.toNat }

/-- The state after an observed word. -/
def probeRun (J M : ℕ) (w : List Bool) : ProbeState := w.foldl (probeStep J M) (probeInit M)

/-- The probe's reader: flip the coin under test. -/
def probeReader (J M : ℕ) : Reader := fun w => (probeRun J M w).coin

/-- Completed coins according to an observed word. -/
def probeWordCompleted (J M : ℕ) (w : List Bool) : ℕ := (probeRun J M w).count

theorem probeRun_append (J M : ℕ) (w : List Bool) (b : Bool) :
    probeRun J M (w ++ [b]) = probeStep J M (probeRun J M w) b := by
  unfold probeRun
  rw [List.foldl_append]
  rfl

theorem probeResolved_iff (J k : ℕ) (ω : ℕ → Bool) :
    probeResolved J k (tailHeads (4 ^ k) ω) = true ↔ tailResolvedAt J k ω := by
  unfold probeResolved tailResolvedAt
  exact decide_eq_true_iff

theorem tailHeads_succ (n : ℕ) (ω : ℕ → Bool) :
    tailHeads (n + 1) ω = tailHeads n ω + (ω n).toNat := by
  unfold tailHeads
  rw [Finset.sum_range_succ]

theorem tapeDrop_zero (ω : ℕ → Bool) : tapeDrop 0 ω = ω := by
  funext k
  simp [tapeDrop]

theorem tapeDrop_one_drop (n : ℕ) (ω : ℕ → Bool) :
    tapeDrop 1 (tapeDrop n ω) = tapeDrop (n + 1) ω := by
  funext k
  simp only [tapeDrop]
  congr 1
  omega

/-- Reading one more flip appends it to the observed word and advances the
tape of the chosen coin. -/
theorem readBlock_succ_snoc (n : ℕ) (p : Reader) (s : Table) :
    readBlock (n + 1) p s =
      ((readBlock n p s).1 ++ [(readBlock n p s).2 (p (readBlock n p s).1) 0],
        Function.update (readBlock n p s).2 (p (readBlock n p s).1)
          (tapeDrop 1 ((readBlock n p s).2 (p (readBlock n p s).1)))) := by
  induction n generalizing p s with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun xs => p (s (p []) 0 :: xs))
      (Function.update s (p []) (tapeDrop 1 (s (p []))))
    change (s (p []) 0 :: (readBlock (n + 1) (fun xs => p (s (p []) 0 :: xs))
        (Function.update s (p []) (tapeDrop 1 (s (p []))))).1,
      (readBlock (n + 1) (fun xs => p (s (p []) 0 :: xs))
        (Function.update s (p []) (tapeDrop 1 (s (p []))))).2) = _
    rw [h]
    rfl

/-- A shorter block is a prefix of a longer block of the same reader. -/
theorem readBlock_take (p : Reader) (s : Table) {n m : ℕ} (h : n ≤ m) :
    ((readBlock m p s).1).take n = (readBlock n p s).1 := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    rfl
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · rw [readBlock_succ_snoc]
      have hlen : (readBlock m p s).1.length = m := readBlock_length m p s
      rw [List.take_append_of_le_length (by omega)]
      exact ih (by omega)
    · have hn : n = m + 1 := by omega
      subst hn
      have hlen : (readBlock (m + 1) p s).1.length = m + 1 := readBlock_length _ p s
      rw [List.take_of_length_le (by omega)]

theorem probeCompleted_zero (J M : ℕ) (s : Table) : probeCompleted J 0 M s = 0 :=
  Nat.le_zero.mp (probeCompleted_le_budget J 0 M s)

/-- The completed count when `n` coins are admitted and exactly `n` fit. -/
theorem probeCompleted_eq {J M t n : ℕ} {s : Table} (hadm : probeAdmits J M s n)
    (h1 : probeWork J s n ≤ t) (h2 : t < probeWork J s (n + 1)) :
    probeCompleted J t M s = n := by
  apply le_antisymm
  · by_contra hc
    have hr := (le_probeCompleted_iff J t M s (n + 1)).1 (by omega)
    have := hr.2
    omega
  · exact (le_probeCompleted_iff J t M s n).2 ⟨hadm, h1⟩

/-- One more flip does not change the count while the coin under test, coin
`i`, is unfinished. -/
theorem probeCompleted_step_unfinished {J M t i : ℕ} {s : Table} (h1 : probeWork J s i ≤ t)
    (h2 : t + 1 < probeWork J s (i + 1)) :
    probeCompleted J (t + 1) M s = probeCompleted J t M s := by
  apply le_antisymm
  · have hr := probeCompleted_reaches J (t + 1) M s
    apply (le_probeCompleted_iff J t M s _).2
    refine ⟨hr.1, ?_⟩
    have hle : probeCompleted J (t + 1) M s ≤ i := by
      by_contra hc
      have hmono := probeWork_mono J s (show i + 1 ≤ probeCompleted J (t + 1) M s by omega)
      have := hr.2
      omega
    exact (probeWork_mono J s hle).trans h1
  · exact probeCompleted_mono J s (Nat.le_succ t) le_rfl

/-- One more flip does not change the count once the probe has stopped. -/
theorem probeCompleted_step_stopped {J M t i : ℕ} {s : Table} (h1 : probeWork J s i ≤ t)
    (hstop : ¬ probeAdmits J M s (i + 1)) :
    probeCompleted J (t + 1) M s = probeCompleted J t M s := by
  apply le_antisymm
  · have hr := probeCompleted_reaches J (t + 1) M s
    apply (le_probeCompleted_iff J t M s _).2
    refine ⟨hr.1, ?_⟩
    have hle : probeCompleted J (t + 1) M s ≤ i := by
      by_contra hc
      exact hstop (probeAdmits_of_le hr.1 (by omega))
    exact (probeWork_mono J s hle).trans h1
  · exact probeCompleted_mono J s (Nat.le_succ t) le_rfl

/-- Admitting one more coin: the coin cap allows it and the previous coin is
resolved. -/
theorem probeAdmits_succ (J M : ℕ) (s : Table) (n : ℕ) :
    probeAdmits J M s (n + 2) ↔
      probeAdmits J M s (n + 1) ∧ n + 2 ≤ M ∧ ¬ tailUnresolved J (s n) := by
  unfold probeAdmits
  constructor
  · rintro ⟨hM, h⟩
    exact ⟨⟨by omega, fun i hi => h i (by omega)⟩, hM, h n (by omega)⟩
  · rintro ⟨⟨-, h⟩, hM, hn⟩
    refine ⟨hM, fun i hi => ?_⟩
    rcases Nat.lt_or_ge (i + 1) (n + 1) with hlt | hge
    · exact h i hlt
    · have hin : i = n := by omega
      rw [hin]
      exact hn

theorem probeAdmits_one (J M : ℕ) (s : Table) : probeAdmits J M s 1 ↔ 1 ≤ M := by
  unfold probeAdmits
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun i hi => absurd hi (by omega)⟩

/-- The reader's state after `t` flips, against the tape-level probe on the
original table `s`. `tbl` is the table of tapes that remain to be read. -/
structure ProbeInv (J M : ℕ) (s : Table) (t : ℕ) (st : ProbeState) (tbl : Table) : Prop where
  /-- The flips bought are those of the finished coins and of the coin under test. -/
  time : probeWork J s st.coin + st.len = t
  heads : st.heads = tailHeads st.len (s st.coin)
  len_lt : st.len < 4 ^ st.level
  /-- No earlier checkpoint ended the test of the coin under test. -/
  level_le : st.level ≤ tailStop J (s st.coin)
  tape : tbl st.coin = tapeDrop st.len (s st.coin)
  /-- Later coins are untouched. -/
  fresh : ∀ j, st.coin < j → tbl j = s j
  count : st.count = probeCompleted J t M s
  stopped : st.stopped = true ↔ ¬ probeAdmits J M s (st.coin + 1)

theorem probeInv_zero (J M : ℕ) (s : Table) : ProbeInv J M s 0 (probeInit M) s where
  time := by simp [probeInit, probeWork_zero]
  heads := by simp [probeInit, tailHeads]
  len_lt := by simp [probeInit]
  level_le := Nat.zero_le _
  tape := (tapeDrop_zero (s 0)).symm
  fresh := fun _ _ => rfl
  count := (probeCompleted_zero J M s).symm
  stopped := by
    change decide (M = 0) = true ↔ ¬ probeAdmits J M s 1
    rw [decide_eq_true_iff, probeAdmits_one]
    omega

/-- One more flip of the coin under test preserves the invariant. -/
theorem probeInv_step {J M : ℕ} {s : Table} {t : ℕ} {st : ProbeState} {tbl : Table}
    (h : ProbeInv J M s t st tbl) :
    ProbeInv J M s (t + 1) (probeStep J M st (tbl st.coin 0))
      (Function.update tbl st.coin (tapeDrop 1 (tbl st.coin))) := by
  have hb : tbl st.coin 0 = s st.coin st.len := by
    rw [h.tape]
    simp [tapeDrop]
  have hheads : st.heads + (tbl st.coin 0).toNat = tailHeads (st.len + 1) (s st.coin) := by
    rw [hb, tailHeads_succ, h.heads]
  have hwork : probeWork J s (st.coin + 1) =
      probeWork J s st.coin + 4 ^ tailStop J (s st.coin) := probeWork_succ J s st.coin
  have hpow : 4 ^ st.level ≤ 4 ^ tailStop J (s st.coin) :=
    Nat.pow_le_pow_right (by norm_num) h.level_le
  have htape : Function.update tbl st.coin (tapeDrop 1 (tbl st.coin)) st.coin =
      tapeDrop (st.len + 1) (s st.coin) := by
    rw [Function.update_self, h.tape, tapeDrop_one_drop]
  have hfresh : ∀ j, st.coin < j →
      Function.update tbl st.coin (tapeDrop 1 (tbl st.coin)) j = s j := by
    intro j hj
    rw [Function.update_of_ne (by omega)]
    exact h.fresh j hj
  have hlen := h.len_lt
  have htime := h.time
  have h1le : probeWork J s st.coin ≤ t := by omega
  unfold probeStep
  by_cases h1 : st.len + 1 = 4 ^ st.level
  · rw [ite_eq_left h1, hheads, h1]
    by_cases hc : J ≤ st.level ∨
        probeResolved J st.level (tailHeads (4 ^ st.level) (s st.coin)) = true
    · -- The test of the coin under test ends here.
      rw [ite_eq_left hc]
      have hmem : J ≤ st.level ∨ tailResolvedAt J st.level (s st.coin) :=
        hc.imp_right (probeResolved_iff J st.level (s st.coin)).1
      have hlevel : st.level = tailStop J (s st.coin) :=
        le_antisymm h.level_le (Nat.sInf_le hmem)
      have hnext : probeWork J s (st.coin + 1) = t + 1 := by
        rw [hwork, ← hlevel]
        omega
      have hnext2 : t + 1 < probeWork J s (st.coin + 1 + 1) := by
        have h2 := probeWork_succ J s (st.coin + 1)
        have h3 := tailWork_pos J (s (st.coin + 1))
        omega
      have hunres : probeResolved J st.level (tailHeads (4 ^ st.level) (s st.coin)) = true ↔
          ¬ tailUnresolved J (s st.coin) := by
        rw [probeResolved_iff, tailUnresolved_iff, ← hlevel, not_not]
      refine ⟨by simpa using hnext, by simp [tailHeads], by simp, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
      · change Function.update tbl st.coin (tapeDrop 1 (tbl st.coin)) (st.coin + 1) =
          tapeDrop 0 (s (st.coin + 1))
        rw [hfresh _ (Nat.lt_succ_self _), tapeDrop_zero]
      · intro j hj
        exact hfresh j (by
          have : st.coin + 1 < j := hj
          omega)
      · change (if st.stopped = true then st.count else st.count + 1) =
          probeCompleted J (t + 1) M s
        by_cases hs : st.stopped = true
        · rw [ite_eq_left hs, h.count]
          exact (probeCompleted_step_stopped h1le (h.stopped.1 hs)).symm
        · have hadm : probeAdmits J M s (st.coin + 1) := by
            by_contra hn
            exact hs (h.stopped.2 hn)
          have hbefore : probeCompleted J t M s = st.coin :=
            probeCompleted_eq (probeAdmits_of_le hadm (Nat.le_succ _)) h1le (by omega)
          have hafter : probeCompleted J (t + 1) M s = st.coin + 1 :=
            probeCompleted_eq hadm hnext.le hnext2
          rw [ite_eq_right hs, h.count, hbefore, hafter]
      · change (st.stopped ||
            !probeResolved J st.level (tailHeads (4 ^ st.level) (s st.coin)) ||
            decide (M < st.coin + 2)) = true ↔ ¬ probeAdmits J M s (st.coin + 1 + 1)
        rw [probeAdmits_succ, Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_true_iff]
        constructor
        · rintro ((hs | hr) | hM) ⟨hadm, hle, hres⟩
          · exact h.stopped.1 hs hadm
          · rw [← Bool.not_eq_true, hunres] at hr
            exact hr hres
          · omega
        · intro hn
          by_cases hs : st.stopped = true
          · exact Or.inl (Or.inl hs)
          · have hadm : probeAdmits J M s (st.coin + 1) := by
              by_contra hna
              exact hs (h.stopped.2 hna)
            by_cases hM : M < st.coin + 2
            · exact Or.inr hM
            · refine Or.inl (Or.inr ?_)
              rw [← Bool.not_eq_true, hunres]
              exact fun hres => hn ⟨hadm, by omega, hres⟩
    · -- The checkpoint is passed and the test continues.
      rw [ite_eq_right hc]
      have hne : st.level ≠ tailStop J (s st.coin) := by
        intro heq
        apply hc
        rcases tailStop_mem J (s st.coin) with hJ | hres
        · exact Or.inl (heq ▸ hJ)
        · exact Or.inr ((probeResolved_iff J st.level (s st.coin)).2 (heq ▸ hres))
      have hlt : st.level < tailStop J (s st.coin) := lt_of_le_of_ne h.level_le hne
      have hpow2 : 4 ^ (st.level + 1) ≤ 4 ^ tailStop J (s st.coin) :=
        Nat.pow_le_pow_right (by norm_num) hlt
      have hsucc : 4 ^ (st.level + 1) = 4 ^ st.level * 4 := pow_succ 4 st.level
      have hpos : 0 < 4 ^ st.level := pow_pos (by norm_num) st.level
      refine ⟨?_, rfl, ?_, hlt, ?_, hfresh, ?_, h.stopped⟩
      · change probeWork J s st.coin + 4 ^ st.level = t + 1
        omega
      · change 4 ^ st.level < 4 ^ (st.level + 1)
        omega
      · change Function.update tbl st.coin (tapeDrop 1 (tbl st.coin)) st.coin =
          tapeDrop (4 ^ st.level) (s st.coin)
        rw [← h1]
        exact htape
      · change st.count = probeCompleted J (t + 1) M s
        rw [h.count]
        exact (probeCompleted_step_unfinished h1le (by omega)).symm
  · -- Not a checkpoint.
    rw [ite_eq_right h1]
    refine ⟨?_, hheads, ?_, h.level_le, htape, hfresh, ?_, h.stopped⟩
    · change probeWork J s st.coin + (st.len + 1) = t + 1
      omega
    · change st.len + 1 < 4 ^ st.level
      omega
    · change st.count = probeCompleted J (t + 1) M s
      rw [h.count]
      exact (probeCompleted_step_unfinished h1le (by omega)).symm

/-- After the reader has bought `t` flips, its state matches the tape-level
probe at flip budget `t`. -/
theorem probeInv_readBlock (J M : ℕ) (s : Table) (t : ℕ) :
    ProbeInv J M s t (probeRun J M (readBlock t (probeReader J M) s).1)
      (readBlock t (probeReader J M) s).2 := by
  induction t with
  | zero => exact probeInv_zero J M s
  | succ t ih =>
    rw [readBlock_succ_snoc]
    change ProbeInv J M s (t + 1)
      (probeRun J M ((readBlock t (probeReader J M) s).1 ++
        [(readBlock t (probeReader J M) s).2
          (probeRun J M (readBlock t (probeReader J M) s).1).coin 0]))
      (Function.update (readBlock t (probeReader J M) s).2
        (probeRun J M (readBlock t (probeReader J M) s).1).coin
        (tapeDrop 1 ((readBlock t (probeReader J M) s).2
          (probeRun J M (readBlock t (probeReader J M) s).1).coin)))
    rw [probeRun_append]
    exact probeInv_step ih

/-- The schedule of the reader. After `t` flips the reader is on the first
coin whose test is not complete within `t` flips. So it buys the
`tailWork J (s i)` flips of coin `i` consecutively, as the single-coin test
does, and it never returns to a coin. -/
theorem probeReader_schedule (J M : ℕ) (s : Table) (t : ℕ) :
    probeWork J s (probeReader J M (readBlock t (probeReader J M) s).1) ≤ t ∧
      t < probeWork J s (probeReader J M (readBlock t (probeReader J M) s).1 + 1) := by
  have h := probeInv_readBlock J M s t
  have hpow : 4 ^ (probeRun J M (readBlock t (probeReader J M) s).1).level ≤
      4 ^ tailStop J (s (probeRun J M (readBlock t (probeReader J M) s).1).coin) :=
    Nat.pow_le_pow_right (by norm_num) h.level_le
  have hwork : probeWork J s ((probeRun J M (readBlock t (probeReader J M) s).1).coin + 1) =
      probeWork J s (probeRun J M (readBlock t (probeReader J M) s).1).coin +
        4 ^ tailStop J (s (probeRun J M (readBlock t (probeReader J M) s).1).coin) :=
    probeWork_succ J s _
  have h1 := h.time
  have h2 := h.len_lt
  change probeWork J s (probeRun J M (readBlock t (probeReader J M) s).1).coin ≤ t ∧
    t < probeWork J s ((probeRun J M (readBlock t (probeReader J M) s).1).coin + 1)
  constructor <;> omega

/-- The count computed from the observed word of a block of `b` flips is the
probe's completed count at flip budget `b`. -/
theorem probeWordCompleted_readBlock (J M b : ℕ) (s : Table) :
    probeWordCompleted J M (readBlock b (probeReader J M) s).1 = probeCompleted J b M s :=
  (probeInv_readBlock J M s b).count

/-- Pause and resume. The count computed from the first `t` observed flips of a
longer block is the probe's completed count at flip budget `t`. -/
theorem probeWordCompleted_take (J M : ℕ) (s : Table) {t b : ℕ} (h : t ≤ b) :
    probeWordCompleted J M (((readBlock b (probeReader J M) s).1).take t) =
      probeCompleted J t M s := by
  rw [readBlock_take _ _ h]
  exact probeWordCompleted_readBlock J M t s

end ThresholdHC.ArbitraryLawAdaptation
