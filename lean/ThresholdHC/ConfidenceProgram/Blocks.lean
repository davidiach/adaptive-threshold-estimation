import ThresholdHC.HardBudget.Words

noncomputable section
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.HardBudget

/-- A sequence of equal-sized blocks uses pair-numbered, disjoint coin labels. -/
def blockReader (N : ℕ) (p : ℕ → Reader) (k start : ℕ) : Reader :=
  match k with
  | 0 => fun _ => 0
  | j+1 => thenRead N (Nat.pair start ∘ p start) (blockReader N p j (start+1))

def blockWords (N : ℕ) (p : ℕ → Reader) (s : Table) (k start : ℕ) : List Bool :=
  match k with
  | 0 => []
  | j+1 => (readBlock N (p start) (s ∘ Nat.pair start)).1 ++ blockWords N p s j (start+1)

private theorem blockWords_congr (N : ℕ) (p : ℕ → Reader) (s t : Table) (k start : ℕ)
    (h : ∀ i ≥ start, ∀ c, s (Nat.pair i c) = t (Nat.pair i c)) :
    blockWords N p s k start = blockWords N p t k start := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    have he : s ∘ Nat.pair start = t ∘ Nat.pair start := funext (h start le_rfl)
    simp only [blockWords,he]
    rw [ih (start+1) (fun i hi => h i (by omega))]

theorem independent_words (N : ℕ) (p : ℕ → Reader) (s : Table) (k start : ℕ) :
    (readBlock (k*N) (blockReader N p k start) s).1 = blockWords N p s k start := by
  induction k generalizing start s with
  | zero => simp [readBlock,blockWords]
  | succ k ih =>
    let tag := Nat.pair start
    let v := readBlock N (tag ∘ p start) s
    have hsame (i : ℕ) (hi : i ≥ start+1) (c : ℕ) :
        v.2 (Nat.pair i c) = s (Nat.pair i c) := by
      apply readBlock_untouched; intro w he
      have h := (Nat.pair_eq_pair.mp he).1
      omega
    have hhead := readBlock_relabel N tag (fun _ _ h => (Nat.pair_eq_pair.mp h).2) (p start) s
    rw [Nat.succ_mul,Nat.add_comm,blockReader,readBlock_append]
    change v.1 ++ (readBlock (k*N) (blockReader N p k (start+1)) v.2).1 = _
    rw [ih,blockWords_congr N p v.2 s k (start+1) hsame,show v.1 = _ from hhead]
    rfl

def blockAt (N : ℕ) (i : ℕ) (xs : List Bool) : List Bool :=
  match i with
  | 0 => xs.take N
  | j+1 => blockAt N j (xs.drop N)

theorem observed_block (N : ℕ) (p : ℕ → Reader) (s : Table) (k start i : ℕ) (hi : i < k) :
    blockAt N i (readBlock (k*N) (blockReader N p k start) s).1 =
      (readBlock N (p (start+i)) (s ∘ Nat.pair (start+i))).1 := by
  rw [independent_words]
  induction k generalizing start i with
  | zero => omega
  | succ k ih =>
    let w := (readBlock N (p start) (s ∘ Nat.pair start)).1
    have hl : w.length = N := readBlock_length _ _ _
    change blockAt N i (w++blockWords N p s k (start+1)) = _
    cases i with
    | zero => simp only [blockAt,Nat.add_zero]; rw [← hl,List.take_left,hl]
    | succ i =>
      rw [blockAt,← hl,List.drop_left,hl]
      have h := ih (start+1) i (by omega)
      simpa only [show start+1+i = start+(i+1) by omega] using h

end ThresholdHC.ConfidenceProgram
