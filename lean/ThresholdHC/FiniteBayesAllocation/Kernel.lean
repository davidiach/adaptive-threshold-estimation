import ThresholdHC.FiniteBayesAllocation.Specification

/-! Natural-number encoding of the horizon-eight word weights, evaluated by the
kernel in the certificate modules.

For an ordered word `u` of eight flips, `labelsOf 8 p u` lists the labels the
policy `p` queries, and `countsOf p u` lists the head and tail counts of the
labels `0, ..., 7`. A case code stores, with a common denominator `den`, the
numbers `pos k j = den * m_j * q_k(d_j)` and `neg k j = den * m_j * (1 - q_k(d_j))`,
the heads probabilities `up j / 32 = 1/2 + d_j` and `dn j / 32 = 1/2 - d_j`, and
`tt k = 16 * θ_k`. Then `wordNat C k (countsOf p u) / (den * 32^8)^8` is the
weight of `u` under the sign law `k` (proved in `Atoms`). For each word,
`statsOf` returns `(A, B, C) = (Σ a_k, Σ a_k tt_k, Σ a_k tt_k^2)`, from which
the word's evidence-weighted posterior variance `Σ_k w_k (mean - θ_k)^2`
equals `(A C - B^2) / (256 (den 32^8)^8 A)`; `certify` returns the floor and
ceiling sums of that quantity at precision `10^20`,
together with a flag recording that every word passed its inequality check. -/

namespace ThresholdHC.FiniteBayesAllocation

/-- All ordered words of length `n`. -/
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (allWords n).map (List.cons false) ++ (allWords n).map (List.cons true)

/-- Labels of the first `n` flips of the ordered word `u` under the reader `p`. -/
def labelsOf (n : ℕ) (p : List Bool → ℕ) (u : List Bool) : List ℕ :=
  List.ofFn fun t : Fin n => p (u.take t)

/-- Number of heads on label `i` in a list of label and outcome pairs. -/
def headCount (z : List (ℕ × Bool)) (i : ℕ) : ℕ := z.countP fun lb => decide (lb.1 = i) && lb.2

/-- Number of tails on label `i` in a list of label and outcome pairs. -/
def tailCount (z : List (ℕ × Bool)) (i : ℕ) : ℕ := z.countP fun lb => decide (lb.1 = i) && !lb.2

/-- Head and tail counts of the labels `0, ..., 7` along an ordered word. -/
def countsOf (p : List Bool → ℕ) (u : List Bool) : List (ℕ × ℕ) :=
  let z := (labelsOf 8 p u).zip u
  List.ofFn fun i : Fin 8 => (headCount z i, tailCount z i)

/-- Integer data of a finite atomic case. -/
structure Code (J K : ℕ) where
  den : ℕ
  pos : Fin K → Fin J → ℕ
  neg : Fin K → Fin J → ℕ
  up : Fin J → ℕ
  dn : Fin J → ℕ
  tt : Fin K → ℕ

/-- Scaled likelihood of one label with `ht.1` heads and `ht.2` tails. -/
def localNat {J K : ℕ} (C : Code J K) (k : Fin K) (ht : ℕ × ℕ) : ℕ :=
  (List.ofFn fun j : Fin J => C.pos k j * C.up j ^ ht.1 * C.dn j ^ ht.2 +
    C.neg k j * C.dn j ^ ht.1 * C.up j ^ ht.2).sum * 32 ^ (8 - (ht.1 + ht.2))

/-- Scaled weight of a word with the given label counts. -/
def wordNat {J K : ℕ} (C : Code J K) (k : Fin K) (cs : List (ℕ × ℕ)) : ℕ :=
  (cs.map (localNat C k)).prod

/-- The three moments `(Σ a_k, Σ a_k tt_k, Σ a_k tt_k^2)` of a word. -/
def statsOf {J K : ℕ} (C : Code J K) (cs : List (ℕ × ℕ)) : ℕ × ℕ × ℕ :=
  let a := List.ofFn fun k : Fin K => (wordNat C k cs, C.tt k)
  ((a.map fun x => x.1).sum, (a.map fun x => x.1 * x.2).sum, (a.map fun x => x.1 * x.2 * x.2).sum)

/-- Moments of every ordered word of length eight under the reader `p`. -/
def run {J K : ℕ} (C : Code J K) (p : List Bool → ℕ) : List (ℕ × ℕ × ℕ) :=
  (allWords 8).map fun u => statsOf C (countsOf p u)

/-- The common scale `256 (den 32^8)^8`. -/
def scaleOf {J K : ℕ} (C : Code J K) : ℕ := 256 * (C.den * 32 ^ 8) ^ 8

/-- Certificate precision. -/
def prec : ℕ := 10 ^ 20

/-- Floor of the scaled posterior variance of a word. -/
def lowerTerm (c : ℕ) (s : ℕ × ℕ × ℕ) : ℕ := prec * (s.1 * s.2.2 - s.2.1 * s.2.1) / (c * s.1)

/-- Ceiling of the scaled posterior variance of a word. -/
def upperTerm (c : ℕ) (s : ℕ × ℕ × ℕ) : ℕ :=
  (prec * (s.1 * s.2.2 - s.2.1 * s.2.1) + (c * s.1 - 1)) / (c * s.1)

/-- The two rounding inequalities of a word, checked without subtraction. -/
def wordOK (c : ℕ) (s : ℕ × ℕ × ℕ) : Bool :=
  0 < s.1 && lowerTerm c s * (c * s.1) + prec * (s.2.1 * s.2.1) ≤ prec * (s.1 * s.2.2) &&
    prec * (s.1 * s.2.2) ≤ upperTerm c s * (c * s.1) + prec * (s.2.1 * s.2.1)

/-- Floor sum, ceiling sum and the conjunction of the word checks. -/
def certify (c : ℕ) : List (ℕ × ℕ × ℕ) → ℕ × ℕ × Bool
  | [] => (0, 0, true)
  | s :: ss =>
    let r := certify c ss
    (lowerTerm c s + r.1, upperTerm c s + r.2.1, wordOK c s && r.2.2)

/-- Two scales: masses `8/64, 56/64`, gaps `1/32, 1/4`, the six locked sign laws. -/
def twoCode : Code 2 6 where
  den := 64
  pos := ![![0, 0], ![4, 0], ![8, 0], ![0, 4], ![0, 8], ![1, 7]]
  neg := ![![8, 56], ![4, 56], ![0, 56], ![8, 52], ![8, 48], ![7, 49]]
  up := ![17, 24]
  dn := ![15, 8]
  tt := ![0, 1, 2, 1, 2, 2]

/-- Three scales: masses `8/128, 24/128, 96/128`, gaps `1/32, 1/8, 1/2`, the
seven locked sign laws. -/
def threeCode : Code 3 7 where
  den := 128
  pos := ![![0, 0, 0], ![8, 0, 0], ![0, 8, 0], ![0, 16, 0], ![0, 0, 8], ![0, 0, 16], ![1, 3, 12]]
  neg := ![![8, 24, 96], ![0, 24, 96], ![8, 16, 96], ![8, 8, 96], ![8, 24, 88], ![8, 24, 80],
    ![7, 21, 84]]
  up := ![17, 20, 32]
  dn := ![15, 12, 0]
  tt := ![0, 1, 1, 2, 1, 2, 2]

theorem certify_eq (c : ℕ) (L : List (ℕ × ℕ × ℕ)) :
    certify c L = ((L.map (lowerTerm c)).sum, (L.map (upperTerm c)).sum, L.all (wordOK c)) := by
  induction L with
  | nil => rfl
  | cons s L ih => simp only [certify, ih, List.map_cons, List.sum_cons, List.all_cons]

theorem certify_spec {c lo hi : ℕ} {L : List (ℕ × ℕ × ℕ)} (h : certify c L = (lo, hi, true)) :
    (L.map (lowerTerm c)).sum = lo ∧ (L.map (upperTerm c)).sum = hi ∧
      ∀ s ∈ L, wordOK c s = true := by
  rw [certify_eq] at h
  simp only [Prod.mk.injEq, List.all_eq_true] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem wordOK_spec {c : ℕ} {s : ℕ × ℕ × ℕ} (h : wordOK c s = true) :
    0 < s.1 ∧ lowerTerm c s * (c * s.1) + prec * (s.2.1 * s.2.1) ≤ prec * (s.1 * s.2.2) ∧
      prec * (s.1 * s.2.2) ≤ upperTerm c s * (c * s.1) + prec * (s.2.1 * s.2.1) := by
  simp only [wordOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end ThresholdHC.FiniteBayesAllocation
