import ThresholdHC.RepeatedCheck.Specification

/-! The survivor rows behind display (29) of
`research/2026-10-30-confidence-transfer/ANYTIME.md`, as computable natural
number lists.

`crossNat n k` is the crossing test `12n < (4k - n)²` in `ℕ` (one of the two
truncated differences vanishes). Row `n` lists, for each head count `k ≤ n`,
the survivor weight: the number of head/tail paths of length `n` with `k`
heads that never crossed at lengths `1, …, n`, each weighted by `3` per tail.
A tail keeps the head count and multiplies the weight by `3`, a head raises the
head count and keeps the weight; crossed entries are set to `0`. This is the
integer path count of the package verifier `verify_anytime.py`.

`stepAux` makes one pass over the previous row, so the kernel evaluates each
entry once; the lemma `survivor_succ` is the recurrence in index form. -/

namespace ThresholdHC.RepeatedCheck

/-- The crossing test `12n < (4k - n)²` in `ℕ`. -/
def crossNat (n k : ℕ) : Bool := decide (12 * n < (4 * k - n) ^ 2 + (n - 4 * k) ^ 2)

theorem crossNat_iff (n k : ℕ) :
    crossNat n k = true ↔ 12 * (n : ℝ) < (4 * (k : ℝ) - n) ^ 2 := by
  unfold crossNat
  rw [decide_eq_true_iff]
  rcases le_total n (4 * k) with h | h
  · rw [Nat.sub_eq_zero_of_le h]
    have hc : (4 * (k : ℝ) - n) = ((4 * k - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub h]
      push_cast
      ring
    rw [hc]
    norm_cast
  · rw [Nat.sub_eq_zero_of_le h]
    have hc : (4 * (k : ℝ) - n) ^ 2 = ((n - 4 * k : ℕ) : ℝ) ^ 2 := by
      rw [Nat.cast_sub h]
      push_cast
      ring
    rw [hc]
    norm_cast
    simp

/-- One pass of the survivor recursion. At position `k` the new entry is
`3 * (old entry k) + (old entry k-1)`, or `0` if `(m, k)` crosses (`m` is the
length of the new row); `prev` is the old entry at `k - 1`. -/
def stepAux (m : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | k, prev, [] => [cond (crossNat m k) 0 prev]
  | k, prev, a :: l => cond (crossNat m k) 0 (3 * a + prev) :: stepAux m (k + 1) a l

/-- The survivor rows: `survivorRow n` has length `n + 1`. -/
def survivorRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => stepAux (n + 1) 0 0 (survivorRow n)

/-- The survivor weight of head count `k` at length `n`. -/
def survivor (n k : ℕ) : ℕ := (survivorRow n).getD k 0

theorem stepAux_length (m : ℕ) (l : List ℕ) :
    ∀ k prev, (stepAux m k prev l).length = l.length + 1 := by
  induction l with
  | nil => intro k prev; rfl
  | cons a l ih =>
    intro k prev
    simp [stepAux, ih]

theorem survivorRow_length (n : ℕ) : (survivorRow n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [survivorRow, stepAux_length, ih]

theorem stepAux_getD (m : ℕ) (l : List ℕ) :
    ∀ k prev j, (stepAux m k prev l).getD j 0 =
      cond (crossNat m (k + j)) 0 (3 * l.getD j 0 + if j = 0 then prev else l.getD (j - 1) 0) := by
  induction l with
  | nil =>
    intro k prev j
    cases j with
    | zero => simp [stepAux]
    | succ j => simp [stepAux]
  | cons a l ih =>
    intro k prev j
    cases j with
    | zero => simp [stepAux]
    | succ j =>
      simp only [stepAux, List.getD_cons_succ]
      rw [ih (k + 1) a j]
      have hk : k + 1 + j = k + (j + 1) := by omega
      rw [hk]
      cases j with
      | zero => simp
      | succ j => simp

theorem survivor_zero (k : ℕ) : survivor 0 k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => rfl
  | succ k => simp [survivor, survivorRow]

theorem survivor_succ (n k : ℕ) :
    survivor (n + 1) k =
      cond (crossNat (n + 1) k) 0 (3 * survivor n k + if k = 0 then 0 else survivor n (k - 1)) := by
  unfold survivor
  rw [survivorRow, stepAux_getD]
  simp

theorem list_sum_eq_range (l : List ℕ) :
    l.sum = ∑ k ∈ Finset.range l.length, l.getD k 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp [add_comm]

theorem survivorRow_sum (n : ℕ) :
    (survivorRow n).sum = ∑ k ∈ Finset.range (n + 1), survivor n k := by
  rw [list_sum_eq_range, survivorRow_length]
  rfl

end ThresholdHC.RepeatedCheck
