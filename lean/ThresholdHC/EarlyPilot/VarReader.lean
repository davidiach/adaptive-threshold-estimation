import ThresholdHC.EarlyPilot.Specification

/-! A sequential reader whose blocks have data-dependent lengths.

Blocks `0, 1, …` run one after another. Block `n` flips the coins
`lab n c` with its own reader `p n`, and it ends after the first observed flip
at which its stopping rule `fin n` holds on the block's word. The state of the
reader after an observed word records the current block, the word observed in
it so far, and the words of the finished blocks. The policy stops after block
`N - 1`.

On a table of coin tapes whose block `n` stops after exactly `ℓ n ≥ 1` flips,
the reader buys `ℓ 0 + … + ℓ (N - 1)` flips, block `n` observes what its
reader would observe alone on the coins `lab n c`, and the path of the policy
is the observed word followed by stop symbols. On an arbitrary word, if every
block's rule holds once the block has `c n ≥ 1` flips, the policy asks for a
flip only below `c 0 + … + c (N - 1)` flips, so that is a pathwise cap. No
probability enters here. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EarlyPilot
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation ThresholdHC.BlindUpper
open ThresholdHC.CriticalEntropy

/-- State of the variable-length reader. -/
structure VarState where
  /-- Index of the current block. -/
  blk : ℕ
  /-- Word observed in the current block. -/
  cur : List Bool
  /-- Words of the finished blocks. -/
  done : List (List Bool)

/-- The initial state. -/
def varStart : VarState := ⟨0, [], []⟩

/-- One observed flip: the current block ends when its rule holds on its word. -/
def varStep (fin : ℕ → List Bool → Bool) (st : VarState) (b : Bool) : VarState :=
  if fin st.blk (st.cur ++ [b]) = true then ⟨st.blk + 1, [], st.done ++ [st.cur ++ [b]]⟩
  else ⟨st.blk, st.cur ++ [b], st.done⟩

/-- The state after an observed word. -/
def varRun (fin : ℕ → List Bool → Bool) (w : List Bool) : VarState :=
  w.foldl (varStep fin) varStart

/-- The reader: the coin that the current block's reader chooses, under the
block's labels. -/
def varReader (fin : ℕ → List Bool → Bool) (lab : ℕ → ℕ → ℕ) (p : ℕ → Reader) : Reader :=
  fun w => lab (varRun fin w).blk (p (varRun fin w).blk (varRun fin w).cur)

/-- The policy: read with `varReader` until `N` blocks are finished. -/
def varPolicy (N : ℕ) (fin : ℕ → List Bool → Bool) (lab : ℕ → ℕ → ℕ) (p : ℕ → Reader)
    (w : List Bool) : Option ℕ :=
  if (varRun fin w).blk < N then some (varReader fin lab p w) else none

/-- The table of block `n`: its coins `lab n c`. -/
def blockTable (lab : ℕ → ℕ → ℕ) (s : Table) (n : ℕ) : Table := fun c => s (lab n c)

theorem varRun_append (fin : ℕ → List Bool → Bool) (w : List Bool) (b : Bool) :
    varRun fin (w ++ [b]) = varStep fin (varRun fin w) b := by
  unfold varRun
  rw [List.foldl_append]
  rfl

theorem varRun_nil (fin : ℕ → List Bool → Bool) : varRun fin [] = varStart := rfl

/-! ### Paths that follow a reader -/

/-- A policy that agrees with `stopAt L q` on every word that `q` observes
within `L` flips has the same path as `stopAt L q`. -/
theorem populationPath_eq_stopAt (pol : List Bool → Option ℕ) (q : Reader) (s : Table)
    (L : ℕ) (h : ∀ t, t ≤ L → pol (readBlock t q s).1 = stopAt L q (readBlock t q s).1) :
    populationPath pol s = populationPath (stopAt L q) s := by
  induction L generalizing pol q s with
  | zero =>
    have h0 : pol [] = stopAt 0 q [] := h 0 le_rfl
    have hs : stopAt 0 q [] = none := by simp [stopAt]
    rw [populationPath_none pol s (h0.trans hs), populationPath_none _ s hs]
  | succ L ih =>
    have hs : stopAt (L + 1) q [] = some (q []) := by simp [stopAt]
    have h0 : pol [] = some (q []) := (h 0 (Nat.zero_le _)).trans hs
    have he : (fun xs => stopAt (L + 1) q (s (q []) 0 :: xs)) =
        stopAt L (fun xs => q (s (q []) 0 :: xs)) := by
      funext xs
      simp [stopAt]
    funext k
    cases k with
    | zero => rw [populationPath_zero, populationPath_zero, h0, hs]
    | succ k =>
      rw [populationPath_succ _ _ _ k h0, populationPath_succ _ _ _ k hs, he]
      refine congrFun (ih _ _ _ fun t ht => ?_) k
      have h1 := h (t + 1) (by omega)
      change pol (s (q []) 0 :: (readBlock t (fun xs => q (s (q []) 0 :: xs))
          (Function.update s (q []) (tapeDrop 1 (s (q []))))).1) =
        stopAt (L + 1) q (s (q []) 0 :: (readBlock t (fun xs => q (s (q []) 0 :: xs))
          (Function.update s (q []) (tapeDrop 1 (s (q []))))).1) at h1
      rw [h1]
      simp [stopAt]

/-! ### The reader on a table of coin tapes -/

section Table

variable (N : ℕ) (fin : ℕ → List Bool → Bool) (lab : ℕ → ℕ → ℕ) (p : ℕ → Reader) (s : Table)
  (ℓ : ℕ → ℕ)

/-- The reader's state after `t` flips on the table `s`, whose block `n` stops
after `ℓ n` flips. `tbl` is the table of tapes that remain to be read. -/
structure VarInv (t : ℕ) (st : VarState) (tbl : Table) : Prop where
  blk_le : st.blk ≤ N
  /-- The flips bought are those of the finished blocks and of the current one. -/
  time : seqOffset ℓ st.blk + st.cur.length = t
  /-- The current block has observed what its reader observes alone. -/
  cur : st.blk < N → st.cur = (readBlock st.cur.length (p st.blk) (blockTable lab s st.blk)).1
  cur_lt : st.blk < N → st.cur.length < ℓ st.blk
  tape : st.blk < N → ∀ c,
    tbl (lab st.blk c) = (readBlock st.cur.length (p st.blk) (blockTable lab s st.blk)).2 c
  /-- Later blocks are untouched. -/
  fresh : ∀ n, st.blk < n → ∀ c, tbl (lab n c) = s (lab n c)
  done : st.done = (List.range st.blk).map (fun n => (readBlock (ℓ n) (p n) (blockTable lab s n)).1)

variable {N lab p s ℓ}

theorem varInv_zero (hℓ : ∀ n, n < N → 0 < ℓ n) : VarInv N lab p s ℓ 0 varStart s where
  blk_le := Nat.zero_le _
  time := by simp [varStart, seqOffset_zero]
  cur := fun _ => rfl
  cur_lt := fun h => hℓ 0 h
  tape := fun _ _ => rfl
  fresh := fun _ _ _ => rfl
  done := rfl

/-- One more flip of the current block preserves the invariant. -/
theorem varInv_step (hlab : ∀ n c n' c', lab n c = lab n' c' → n = n' ∧ c = c')
    (hfin : ∀ n, n < N → ∀ u, fin n (readBlock u (p n) (blockTable lab s n)).1 = true ↔ ℓ n ≤ u)
    (hℓ : ∀ n, n < N → 0 < ℓ n) {t : ℕ} {st : VarState} {tbl : Table}
    (h : VarInv N lab p s ℓ t st tbl) (hblk : st.blk < N) :
    VarInv N lab p s ℓ (t + 1) (varStep fin st (tbl (lab st.blk (p st.blk st.cur)) 0))
      (Function.update tbl (lab st.blk (p st.blk st.cur))
        (tapeDrop 1 (tbl (lab st.blk (p st.blk st.cur))))) := by
  set B := readBlock st.cur.length (p st.blk) (blockTable lab s st.blk) with hB
  set c0 := p st.blk st.cur with hc0def
  have hcur : st.cur = B.1 := h.cur hblk
  have hc0 : c0 = p st.blk B.1 := congrArg (p st.blk) hcur
  have htape : ∀ c, tbl (lab st.blk c) = B.2 c := h.tape hblk
  have hsnoc := readBlock_succ_snoc st.cur.length (p st.blk) (blockTable lab s st.blk)
  rw [← hB] at hsnoc
  have hword : (readBlock (st.cur.length + 1) (p st.blk) (blockTable lab s st.blk)).1 =
      st.cur ++ [tbl (lab st.blk c0) 0] := by
    rw [hsnoc, htape c0, hc0, ← hcur]
  have hne : ∀ n, st.blk ≠ n → ∀ c c', lab n c ≠ lab st.blk c' := fun n hn c c' he =>
    hn (hlab _ _ _ _ he).1.symm
  have hlt := h.cur_lt hblk
  have htime := h.time
  have hiff := hfin st.blk hblk (st.cur.length + 1)
  rw [hword] at hiff
  unfold varStep
  by_cases hf : fin st.blk (st.cur ++ [tbl (lab st.blk c0) 0]) = true
  · -- The block ends here.
    rw [ite_eq_left hf]
    have hend : ℓ st.blk = st.cur.length + 1 := by
      have := hiff.1 hf
      omega
    refine ⟨by simpa using hblk, ?_, fun _ => rfl, fun h1 => hℓ _ h1, ?_, ?_, ?_⟩
    · change seqOffset ℓ (st.blk + 1) + 0 = t + 1
      rw [seqOffset_succ]
      omega
    · intro _ c
      change Function.update tbl (lab st.blk c0) _ (lab (st.blk + 1) c) = s (lab (st.blk + 1) c)
      rw [Function.update_of_ne (hne _ (by omega) _ _)]
      exact h.fresh _ (by omega) c
    · intro n hn c
      change Function.update tbl (lab st.blk c0) _ (lab n c) = s (lab n c)
      have hn' : st.blk + 1 < n := hn
      rw [Function.update_of_ne (hne _ (by omega) _ _)]
      exact h.fresh _ (by omega) c
    · change st.done ++ [st.cur ++ [tbl (lab st.blk c0) 0]] = (List.range (st.blk + 1)).map _
      rw [List.range_succ, List.map_append, h.done, List.map_singleton, hend, hword]
  · -- The block continues.
    rw [ite_eq_right hf]
    have hcont : st.cur.length + 1 < ℓ st.blk := by
      by_contra hc
      exact hf (hiff.2 (by omega))
    have hlen : (st.cur ++ [tbl (lab st.blk c0) 0]).length = st.cur.length + 1 := by simp
    refine ⟨h.blk_le, ?_, fun _ => ?_, fun _ => ?_, fun _ c => ?_, ?_, h.done⟩
    · change seqOffset ℓ st.blk + (st.cur ++ [tbl (lab st.blk c0) 0]).length = t + 1
      rw [hlen]
      omega
    · change st.cur ++ [tbl (lab st.blk c0) 0] =
        (readBlock (st.cur ++ [tbl (lab st.blk c0) 0]).length (p st.blk)
          (blockTable lab s st.blk)).1
      rw [hlen, hword]
    · change (st.cur ++ [tbl (lab st.blk c0) 0]).length < ℓ st.blk
      rw [hlen]
      exact hcont
    · change Function.update tbl (lab st.blk c0) (tapeDrop 1 (tbl (lab st.blk c0)))
          (lab st.blk c) =
        (readBlock (st.cur ++ [tbl (lab st.blk c0) 0]).length (p st.blk)
          (blockTable lab s st.blk)).2 c
      rw [hlen, hsnoc]
      change _ = Function.update B.2 (p st.blk B.1) (tapeDrop 1 (B.2 (p st.blk B.1))) c
      rw [← hc0]
      by_cases hc : c = c0
      · subst hc
        rw [Function.update_self, Function.update_self, htape]
      · have hl : lab st.blk c ≠ lab st.blk c0 := fun he => hc (hlab _ _ _ _ he).2
        rw [Function.update_of_ne hl, Function.update_of_ne hc, htape]
    · intro n hn c
      change Function.update tbl (lab st.blk c0) _ (lab n c) = s (lab n c)
      have hn' : st.blk < n := hn
      rw [Function.update_of_ne (hne _ (by omega) _ _)]
      exact h.fresh _ hn' c

/-- While fewer than `ℓ 0 + … + ℓ (N - 1)` flips are bought the reader is
inside a block below `N`. -/
theorem varInv_blk_lt {t : ℕ} {st : VarState} {tbl : Table} (h : VarInv N lab p s ℓ t st tbl)
    (ht : t < seqOffset ℓ N) : st.blk < N := by
  rcases h.blk_le.lt_or_eq with hlt | heq
  · exact hlt
  · have := h.time
    rw [heq] at this
    omega

/-- Inside a block below `N` fewer than `ℓ 0 + … + ℓ (N - 1)` flips are bought. -/
theorem varInv_lt_of_blk {t : ℕ} {st : VarState} {tbl : Table} (h : VarInv N lab p s ℓ t st tbl)
    (hb : st.blk < N) : t < seqOffset ℓ N := by
  have h1 := h.time
  have h2 := h.cur_lt hb
  have h3 : seqOffset ℓ (st.blk + 1) ≤ seqOffset ℓ N := seqOffset_mono ℓ hb
  rw [seqOffset_succ] at h3
  omega

/-- After `t ≤ ℓ 0 + … + ℓ (N - 1)` flips the reader's state meets the invariant. -/
theorem varInv_readBlock (hlab : ∀ n c n' c', lab n c = lab n' c' → n = n' ∧ c = c')
    (hfin : ∀ n, n < N → ∀ u, fin n (readBlock u (p n) (blockTable lab s n)).1 = true ↔ ℓ n ≤ u)
    (hℓ : ∀ n, n < N → 0 < ℓ n) (t : ℕ) (ht : t ≤ seqOffset ℓ N) :
    VarInv N lab p s ℓ t (varRun fin (readBlock t (varReader fin lab p) s).1)
      (readBlock t (varReader fin lab p) s).2 := by
  induction t with
  | zero => exact varInv_zero hℓ
  | succ t ih =>
    have ih' := ih (by omega)
    have hb := varInv_blk_lt ih' (by omega)
    rw [readBlock_succ_snoc, varRun_append]
    exact varInv_step fin hlab hfin hℓ ih' hb

/-- The state after the whole run: `N` blocks finished, with the words their
readers observe alone. -/
theorem varRun_readBlock_total (hlab : ∀ n c n' c', lab n c = lab n' c' → n = n' ∧ c = c')
    (hfin : ∀ n, n < N → ∀ u, fin n (readBlock u (p n) (blockTable lab s n)).1 = true ↔ ℓ n ≤ u)
    (hℓ : ∀ n, n < N → 0 < ℓ n) :
    (varRun fin (readBlock (seqOffset ℓ N) (varReader fin lab p) s).1).blk = N ∧
      (varRun fin (readBlock (seqOffset ℓ N) (varReader fin lab p) s).1).done =
        (List.range N).map (fun n => (readBlock (ℓ n) (p n) (blockTable lab s n)).1) := by
  have h := varInv_readBlock fin hlab hfin hℓ (seqOffset ℓ N) le_rfl
  have hN : (varRun fin (readBlock (seqOffset ℓ N) (varReader fin lab p) s).1).blk = N := by
    rcases h.blk_le.lt_or_eq with hlt | heq
    · exact absurd (varInv_lt_of_blk h hlt) (lt_irrefl _)
    · exact heq
  exact ⟨hN, by rw [h.done, hN]⟩

/-- The path of the policy on the table: the observed word of the whole run,
followed by stop symbols. -/
theorem populationPath_varPolicy (hlab : ∀ n c n' c', lab n c = lab n' c' → n = n' ∧ c = c')
    (hfin : ∀ n, n < N → ∀ u, fin n (readBlock u (p n) (blockTable lab s n)).1 = true ↔ ℓ n ≤ u)
    (hℓ : ∀ n, n < N → 0 < ℓ n) :
    populationPath (varPolicy N fin lab p) s =
      fun k => (readBlock (seqOffset ℓ N) (varReader fin lab p) s).1[k]? := by
  rw [populationPath_eq_stopAt _ (varReader fin lab p) s (seqOffset ℓ N), block_path]
  intro t ht
  have h := varInv_readBlock fin hlab hfin hℓ t ht
  have hiff : (varRun fin (readBlock t (varReader fin lab p) s).1).blk < N ↔
      (readBlock t (varReader fin lab p) s).1.length < seqOffset ℓ N := by
    rw [readBlock_length]
    exact ⟨varInv_lt_of_blk h, varInv_blk_lt h⟩
  unfold varPolicy stopAt
  by_cases hb : (varRun fin (readBlock t (varReader fin lab p) s).1).blk < N
  · rw [ite_eq_left hb, ite_eq_left (hiff.1 hb)]
  · rw [ite_eq_right hb, ite_eq_right (fun h' => hb (hiff.2 h'))]

end Table

/-! ### A pathwise cap on every word -/

/-- On every word, if the rule of block `n` holds once the block has `c n ≥ 1`
flips, the word is at most the finished blocks' caps plus the current block's
word, which is shorter than its cap. -/
theorem varRun_length_le (fin : ℕ → List Bool → Bool) (c : ℕ → ℕ) (hc : ∀ n, 0 < c n)
    (hfc : ∀ n w, c n ≤ w.length → fin n w = true) (w : List Bool) :
    w.length ≤ seqOffset c (varRun fin w).blk + (varRun fin w).cur.length ∧
      (varRun fin w).cur.length < c (varRun fin w).blk := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨by simp, hc 0⟩
  | append_singleton w b ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [varRun_append]
    unfold varStep
    by_cases hf : fin (varRun fin w).blk ((varRun fin w).cur ++ [b]) = true
    · rw [ite_eq_left hf]
      refine ⟨?_, hc _⟩
      change (w ++ [b]).length ≤ seqOffset c ((varRun fin w).blk + 1) + 0
      rw [seqOffset_succ, List.length_append]
      simp only [List.length_singleton]
      omega
    · rw [ite_eq_right hf]
      have hlt : ((varRun fin w).cur ++ [b]).length < c (varRun fin w).blk := by
        by_contra hge
        exact hf (hfc _ _ (not_lt.mp hge))
      refine ⟨?_, hlt⟩
      change (w ++ [b]).length ≤ seqOffset c (varRun fin w).blk + ((varRun fin w).cur ++ [b]).length
      simp only [List.length_append, List.length_singleton]
      omega

/-- The policy asks for a flip only below `c 0 + … + c (N - 1)` flips. -/
theorem varPolicy_length_lt (N : ℕ) (fin : ℕ → List Bool → Bool) (lab : ℕ → ℕ → ℕ)
    (p : ℕ → Reader) (c : ℕ → ℕ) (hc : ∀ n, 0 < c n)
    (hfc : ∀ n w, c n ≤ w.length → fin n w = true) {w : List Bool}
    (h : (varPolicy N fin lab p w).isSome = true) : w.length < seqOffset c N := by
  have hb : (varRun fin w).blk < N := by
    unfold varPolicy at h
    by_contra hn
    rw [ite_eq_right hn] at h
    exact absurd h (by simp)
  obtain ⟨h1, h2⟩ := varRun_length_le fin c hc hfc w
  have h3 : seqOffset c ((varRun fin w).blk + 1) ≤ seqOffset c N := seqOffset_mono c hb
  rw [seqOffset_succ] at h3
  omega

private theorem history_snoc (x : ProcessTape) (j : ℕ) :
    processHistory x (j + 1) = processHistory x j ++ (x j).toList := by
  unfold processHistory
  rw [List.ofFn_succ']
  cases h : x j <;> simp [processPrefix, List.concat_eq_append, h] <;> rfl

private theorem workOf_history (x : ProcessTape) (j : ℕ) :
    ThresholdHC.workOf (processPrefix j x) = ((processHistory x j).length : ℝ) := by
  induction j with
  | zero => simp [ThresholdHC.workOf, processHistory]
  | succ j ih =>
    rw [processPrefix_snoc, ThresholdHC.Proofs.workOf_snoc, ih, history_snoc, List.length_append]
    cases h : x j <;> simp

/-- A policy that asks for a flip only on words shorter than `n` buys at most
`n` flips on every admissible path. -/
theorem pathwiseCap_of_length {S : Type} [MeasurableSpace S] (A : AdaptiveEstimator S) (n : ℕ)
    (h : ∀ r xs, (A.policy r xs).isSome = true → xs.length < n) : PathwiseCap A n := by
  intro r x hv
  have hlen (j : ℕ) : (processHistory x j).length ≤ n := by
    induction j with
    | zero => simp [processHistory]
    | succ j ih =>
      rw [history_snoc, List.length_append]
      by_cases hj : (processHistory x j).length < n
      · cases x j <;> simp <;> omega
      · have hx := hv j
        have hnone : (A.policy r (processHistory x j)).isSome = false := by
          cases hp : A.policy r (processHistory x j) with
          | none => rfl
          | some a => exact absurd (h r _ (by rw [hp]; rfl)) hj
        rw [hnone] at hx
        have hxj : x j = none := Option.not_isSome_iff_eq_none.mp (by simp [hx])
        rw [hxj]
        simpa using ih
  apply iSup_le
  intro j
  rw [workOf_history, ENNReal.ofReal_natCast]
  exact_mod_cast hlen j

/-- The observed history of a word followed by stop symbols, read past the
word's end, is the word. -/
theorem processHistory_word_le (w : List Bool) {K : ℕ} (hK : w.length ≤ K) :
    processHistory (fun k => w[k]?) K = w := by
  obtain ⟨d, rfl⟩ : ∃ d, K = w.length + d := ⟨K - w.length, by omega⟩
  rw [processHistory_add, processHistory_word]
  have hnone : (fun i => w[w.length + i]?) = fun _ => (none : Option Bool) := by
    funext i
    exact List.getElem?_eq_none (by omega)
  rw [hnone]
  have hempty : processHistory (fun _ => (none : Option Bool)) d = [] := by
    unfold processHistory processPrefix
    simp
  rw [hempty, List.append_nil]

end ThresholdHC.EarlyPilot
