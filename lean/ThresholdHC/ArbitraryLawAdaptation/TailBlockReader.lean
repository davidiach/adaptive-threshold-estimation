import ThresholdHC.ArbitraryLawAdaptation.TailProbeReader
import ThresholdHC.ArbitraryLawAdaptation.TailMedian

/-! Consecutive blocks of observed flips on separate coin labels, and the
median tail certificate as a function of the observed word.

A sequence of blocks runs one after another. Block `n` buys `len n` flips with
its own reader, on the coins `Nat.pair n i`. The part of the observed word that
block `n` bought is then the word its reader would observe alone on those
coins. The construction nests: the reader of a block may itself be a sequence
of blocks.

For the tail certificate, block `j` is probe `j`. The median over the counts
computed from the blocks' words equals the tape-level median certificate of
probes reading the coins `Nat.pair j i`. Cutting the observed word after `t`
flips gives the tape-level median with complete probes, at most one
interrupted probe and probes not yet started. With one more level of blocks,
depth `J` runs its probes on the coins `Nat.pair J (Nat.pair j i)`. No
probability enters here. -/

noncomputable section
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.HardBudget ThresholdHC.CriticalEntropy

/-- Flips bought before block `n`. -/
def seqOffset (len : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, len k

/-- The reader that runs blocks `0, …, n - 1` one after another. Block `k` buys
`len k` flips with the reader `p k`, on the coins `Nat.pair k i`. -/
def seqReader (len : ℕ → ℕ) (p : ℕ → Reader) : ℕ → Reader
  | 0 => fun _ => 0
  | n + 1 => thenRead (seqOffset len n) (seqReader len p n) (Nat.pair n ∘ p n)

/-- The part of an observed word that block `n` bought. -/
def seqWord (len : ℕ → ℕ) (n : ℕ) (w : List Bool) : List Bool :=
  (w.drop (seqOffset len n)).take (len n)

theorem seqOffset_zero (len : ℕ → ℕ) : seqOffset len 0 = 0 := by
  simp [seqOffset]

theorem seqOffset_succ (len : ℕ → ℕ) (n : ℕ) :
    seqOffset len (n + 1) = seqOffset len n + len n :=
  Finset.sum_range_succ _ _

theorem seqOffset_const (b n : ℕ) : seqOffset (fun _ => b) n = n * b := by
  simp [seqOffset]

theorem seqOffset_mono (len : ℕ → ℕ) : Monotone (seqOffset len) :=
  monotone_nat_of_le_succ fun n => by
    rw [seqOffset_succ]
    exact Nat.le_add_right _ _

/-- Blocks already run are not changed by later blocks: on words shorter than
the first `n` blocks, the reader of `n + 1` blocks is the reader of `n`. -/
theorem seqReader_succ_of_lt (len : ℕ → ℕ) (p : ℕ → Reader) (n : ℕ) {xs : List Bool}
    (h : xs.length < seqOffset len n) :
    seqReader len p (n + 1) xs = seqReader len p n xs := by
  change thenRead (seqOffset len n) (seqReader len p n) (Nat.pair n ∘ p n) xs = _
  unfold thenRead
  rw [ite_eq_left h]

/-- The observed word of `N` blocks, block by block. Block `n` observes what
its reader would observe alone on the coins `Nat.pair n i`, and coins of
blocks that have not run are untouched. -/
theorem seqReader_readBlock (len : ℕ → ℕ) (p : ℕ → Reader) (s : Table) (N : ℕ) :
    (∀ n, n < N → seqWord len n (readBlock (seqOffset len N) (seqReader len p N) s).1 =
        (readBlock (len n) (p n) (fun i => s (Nat.pair n i))).1) ∧
      ∀ n, N ≤ n → ∀ i,
        (readBlock (seqOffset len N) (seqReader len p N) s).2 (Nat.pair n i) =
          s (Nat.pair n i) := by
  induction N with
  | zero =>
    refine ⟨fun n hn => absurd hn (Nat.not_lt_zero n), fun n _ i => ?_⟩
    rw [seqOffset_zero]
    rfl
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih
    let v := readBlock (seqOffset len N) (seqReader len p N) s
    let u := readBlock (len N) (Nat.pair N ∘ p N) v.2
    have hW : readBlock (seqOffset len (N + 1)) (seqReader len p (N + 1)) s =
        (v.1 ++ u.1, u.2) := by
      rw [seqOffset_succ]
      exact readBlock_append (seqOffset len N) (len N) (seqReader len p N) (Nat.pair N ∘ p N) s
    have hvlen : v.1.length = seqOffset len N := readBlock_length _ _ _
    have hulen : u.1.length = len N := readBlock_length _ _ _
    have hinj : Function.Injective (Nat.pair N) := fun _ _ h => (Nat.pair_eq_pair.mp h).2
    have hfresh : v.2 ∘ Nat.pair N = fun i => s (Nat.pair N i) := funext (ih2 N le_rfl)
    have hu : u.1 = (readBlock (len N) (p N) (fun i => s (Nat.pair N i))).1 := by
      have h := readBlock_relabel (len N) (Nat.pair N) hinj (p N) v.2
      rw [hfresh] at h
      exact h
    rw [hW]
    refine ⟨fun n hn => ?_, fun n hn i => ?_⟩
    · change ((v.1 ++ u.1).drop (seqOffset len n)).take (len n) = _
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
      · have hoff : seqOffset len n + len n ≤ seqOffset len N := by
          rw [← seqOffset_succ]
          exact seqOffset_mono len hlt
        rw [List.drop_append_of_le_length (by omega),
          List.take_append_of_le_length (by rw [List.length_drop]; omega)]
        exact ih1 n hlt
      · rw [heq, List.drop_left' hvlen, List.take_of_length_le hulen.le]
        exact hu
    · change u.2 (Nat.pair n i) = s (Nat.pair n i)
      have hne : ∀ xs, (Nat.pair N ∘ p N) xs ≠ Nat.pair n i := by
        intro xs h
        have h1 := (Nat.pair_eq_pair.mp h).1
        omega
      rw [readBlock_untouched (len N) (Nat.pair N ∘ p N) v.2 (Nat.pair n i) hne]
      exact ih2 n (by omega) i

/-- Cutting the observed word after `t` flips cuts the word of block `n` after
`t - seqOffset len n` flips. -/
theorem seqWord_take (len : ℕ → ℕ) (n t : ℕ) (w : List Bool) :
    seqWord len n (w.take t) = (seqWord len n w).take (t - seqOffset len n) := by
  unfold seqWord
  rw [List.drop_take, List.take_take, List.take_take, Nat.min_comm]

/-- The median depends only on the first `m` values. -/
theorem blockMedian_congr {m : ℕ} {v v' : ℕ → ℝ} (h : ∀ j, j < m → v j = v' j) :
    blockMedian m v = blockMedian m v' := by
  have hf : (fun j : Fin m => v j) = fun j : Fin m => v' j := funext fun j => h j j.isLt
  unfold blockMedian
  by_cases hm : 0 < m
  · rw [dite_eq_left hm, dite_eq_left hm, hf]
    exact h _ (Fin.isLt _)
  · rw [dite_eq_right hm, dite_eq_right hm]

/-- `m` probes of depth `J` one after another, each with a block of `b` flips
and coin cap `M`. Probe `j` reads the coins `Nat.pair j i`. -/
def medianReader (J M b m : ℕ) : Reader :=
  seqReader (fun _ => b) (fun _ => probeReader J M) m

/-- The median certificate computed from an observed word of `m` blocks of `b`
flips: the median of `probeUpper` of the counts computed from the blocks. -/
def medianWordUpper (J m b M : ℕ) (w : List Bool) : ℝ :=
  blockMedian m (fun j => probeUpper (probeWordCompleted J M (seqWord (fun _ => b) j w)))

/-- The certificate computed from the observed word of the `m` blocks is the
tape-level median certificate of probes with flip budget `b` and coin cap `M`,
probe `j` reading the coins `Nat.pair j i`. -/
theorem medianWordUpper_readBlock (J m b M : ℕ) (s : Table) :
    medianWordUpper J m b M (readBlock (m * b) (medianReader J M b m) s).1 =
      medianUpper J m (fun _ => b) (fun _ => M) (fun j i => s (Nat.pair j i)) := by
  unfold medianWordUpper medianUpper
  apply blockMedian_congr
  intro j hj
  have h := (seqReader_readBlock (fun _ => b) (fun _ => probeReader J M) s m).1 j hj
  rw [seqOffset_const] at h
  change probeUpper (probeWordCompleted J M (seqWord (fun _ => b) j
    (readBlock (m * b) (seqReader (fun _ => b) (fun _ => probeReader J M) m) s).1)) =
    probeUpper (probeCompleted J b M (fun i => s (Nat.pair j i)))
  rw [h, probeWordCompleted_readBlock]

/-- Pause and resume. The certificate computed from the first `t` observed
flips is the tape-level median with probe `j` at flip budget
`min (t - j b) b`: complete probes, at most one interrupted probe, and probes
that have not started. -/
theorem medianWordUpper_take (J m b M t : ℕ) (s : Table) :
    medianWordUpper J m b M ((readBlock (m * b) (medianReader J M b m) s).1.take t) =
      medianUpper J m (fun j => min (t - j * b) b) (fun _ => M)
        (fun j i => s (Nat.pair j i)) := by
  unfold medianWordUpper medianUpper
  apply blockMedian_congr
  intro j hj
  have h := (seqReader_readBlock (fun _ => b) (fun _ => probeReader J M) s m).1 j hj
  rw [seqOffset_const] at h
  change probeUpper (probeWordCompleted J M (seqWord (fun _ => b) j
    ((readBlock (m * b) (seqReader (fun _ => b) (fun _ => probeReader J M) m) s).1.take t))) =
    probeUpper (probeCompleted J (min (t - j * b) b) M (fun i => s (Nat.pair j i)))
  rw [seqWord_take, seqOffset_const, h]
  congr 1
  rcases le_total (t - j * b) b with hle | hle
  · rw [Nat.min_eq_left hle]
    exact probeWordCompleted_take J M _ hle
  · rw [Nat.min_eq_right hle, List.take_of_length_le (by rw [readBlock_length]; exact hle)]
    exact probeWordCompleted_readBlock J M b _

/-- Flips bought by the depths below `N`, where depth `J` runs `m J` probes of
`b J` flips. -/
def depthsCost (m b : ℕ → ℕ) (N : ℕ) : ℕ := seqOffset (fun J => m J * b J) N

/-- The depths `J < N` one after another. Depth `J` runs `m J` probes, each
with `b J` flips and coin cap `M J`. Probe `j` of depth `J` reads the coins
`Nat.pair J (Nat.pair j i)`. -/
def depthsReader (m b M : ℕ → ℕ) (N : ℕ) : Reader :=
  seqReader (fun J => m J * b J) (fun J => medianReader J (M J) (b J) (m J)) N

/-- The certificate of depth `J` computed from an observed word of the depths. -/
def depthWordUpper (m b M : ℕ → ℕ) (J : ℕ) (w : List Bool) : ℝ :=
  medianWordUpper J (m J) (b J) (M J) (seqWord (fun J => m J * b J) J w)

/-- The certificate of depth `J < N` computed from the observed word of the
depths is the tape-level median certificate of the probes of depth `J`, probe
`j` reading the coins `Nat.pair J (Nat.pair j i)`. -/
theorem depthWordUpper_readBlock (m b M : ℕ → ℕ) (N : ℕ) (s : Table) {J : ℕ} (hJ : J < N) :
    depthWordUpper m b M J (readBlock (depthsCost m b N) (depthsReader m b M N) s).1 =
      medianUpper J (m J) (fun _ => b J) (fun _ => M J)
        (fun j i => s (Nat.pair J (Nat.pair j i))) := by
  have h := (seqReader_readBlock (fun J => m J * b J)
    (fun J => medianReader J (M J) (b J) (m J)) s N).1 J hJ
  unfold depthWordUpper
  change medianWordUpper J (m J) (b J) (M J) (seqWord (fun J => m J * b J) J
    (readBlock (seqOffset (fun J => m J * b J) N) (seqReader (fun J => m J * b J)
      (fun J => medianReader J (M J) (b J) (m J)) N) s).1) = _
  rw [h]
  exact medianWordUpper_readBlock J (m J) (b J) (M J) (fun i => s (Nat.pair J i))

/-- Pause and resume across depths. The certificate of depth `J < N` computed
from the first `t` observed flips is the tape-level median with the probes of
depth `J` at the flip budgets they have reached. -/
theorem depthWordUpper_take (m b M : ℕ → ℕ) (N : ℕ) (s : Table) {J : ℕ} (hJ : J < N) (t : ℕ) :
    depthWordUpper m b M J
        ((readBlock (depthsCost m b N) (depthsReader m b M N) s).1.take t) =
      medianUpper J (m J) (fun j => min (t - depthsCost m b J - j * b J) (b J))
        (fun _ => M J) (fun j i => s (Nat.pair J (Nat.pair j i))) := by
  have h := (seqReader_readBlock (fun J => m J * b J)
    (fun J => medianReader J (M J) (b J) (m J)) s N).1 J hJ
  unfold depthWordUpper
  change medianWordUpper J (m J) (b J) (M J) (seqWord (fun J => m J * b J) J
    ((readBlock (seqOffset (fun J => m J * b J) N) (seqReader (fun J => m J * b J)
      (fun J => medianReader J (M J) (b J) (m J)) N) s).1.take t)) = _
  rw [seqWord_take, h]
  exact medianWordUpper_take J (m J) (b J) (M J) (t - depthsCost m b J)
    (fun i => s (Nat.pair J i))

end ThresholdHC.ArbitraryLawAdaptation
