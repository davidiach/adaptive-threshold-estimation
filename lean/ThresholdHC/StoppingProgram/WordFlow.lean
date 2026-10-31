import ThresholdHC.StoppingProgram.TapeMoments

/-! Count weights as sums over the actual ordered prefixes. -/

noncomputable section
open scoped BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy

def shortWord {n : ℕ} (w : Fin n → Bool) (m : ℕ) (hm : m ≤ n) : Fin m → Bool :=
  fun i => w ⟨i.val,lt_of_lt_of_le i.isLt hm⟩

theorem shortWord_self {n : ℕ} (w : Fin n → Bool) : shortWord w n le_rfl = w := by
  funext i
  rfl

theorem shortWord_snoc {n : ℕ} (w : Fin n → Bool) (b : Bool) (m : ℕ) (hm : m ≤ n) :
    shortWord (Fin.snoc w b) m (by omega) = shortWord w m hm := by
  funext i
  change Fin.snoc (α := fun _ : Fin (n+1) => Bool) w b (Fin.castSucc ⟨i.val,lt_of_lt_of_le i.isLt hm⟩) = _
  rw [Fin.snoc_castSucc]
  rfl

theorem wordHeads_sum {n : ℕ} (w : Fin n → Bool) : wordHeads w = ∑ i, if w i then 1 else 0 := by
  simp [wordHeads]

theorem wordHeads_snoc {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    wordHeads (Fin.snoc w b) = wordHeads w+(if b then 1 else 0) := by
  simp only [wordHeads_sum,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

def wordArrival {N n : ℕ} (b : CountState N → Bool) (w : Fin n → Bool) : ℝ :=
  ∏ j : Fin n, (1-countDecision b j.val (wordHeads (shortWord w j.val j.isLt.le)))

theorem wordArrival_snoc {N n : ℕ} (b : CountState N → Bool) (w : Fin n → Bool) (a : Bool) :
    wordArrival b (Fin.snoc w a) = wordArrival b w*(1-countDecision b n (wordHeads w)) := by
  unfold wordArrival
  rw [Fin.prod_univ_castSucc]
  apply congrArg₂ (fun x y : ℝ => x*y)
  · apply Finset.prod_congr rfl
    intro j _
    change 1-countDecision b j.val (wordHeads (shortWord (Fin.snoc w a) j.val _)) = _
    rw [shortWord_snoc w a j.val j.isLt.le]
  · change 1-countDecision b n (wordHeads (shortWord (Fin.snoc w a) n _)) = _
    rw [shortWord_snoc w a n le_rfl,shortWord_self]

def wordArrivalCount {N : ℕ} (b : CountState N → Bool) (n k : ℕ) : ℝ :=
  ∑ w : Fin n → Bool, if wordHeads w = k then wordArrival b w else 0

theorem wordArrivalCount_zero {N : ℕ} (b : CountState N → Bool) (k : ℕ) :
    wordArrivalCount b 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [wordArrivalCount,wordArrival,wordHeads]
  · simp [wordArrivalCount,wordArrival,wordHeads,hk,Ne.symm hk]

theorem wordArrivalCount_succ {N : ℕ} (b : CountState N → Bool) (n k : ℕ) :
    wordArrivalCount b (n+1) k = wordArrivalCount b n k*(1-countDecision b n k)+
      if 0 < k then wordArrivalCount b n (k-1)*(1-countDecision b n (k-1)) else 0 := by
  have he := (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).sum_comp
    (fun w => if wordHeads w = k then wordArrival b w else 0)
  unfold wordArrivalCount at *
  rw [← he,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [Fin.snocEquiv_apply,wordHeads_snoc,wordArrival_snoc,ite_true,Bool.false_eq_true,ite_false,add_zero]
  have hfalse : (∑ w : Fin n → Bool, if wordHeads w = k then wordArrival b w*(1-countDecision b n (wordHeads w)) else 0) =
      (∑ w : Fin n → Bool, if wordHeads w = k then wordArrival b w else 0)*(1-countDecision b n k) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs with hw <;> simp [hw]
  rw [hfalse]
  by_cases hk : 0 < k
  · rw [ite_eq_left hk]
    have htrue : (∑ w : Fin n → Bool, if wordHeads w+1 = k then wordArrival b w*(1-countDecision b n (wordHeads w)) else 0) =
        (∑ w : Fin n → Bool, if wordHeads w = k-1 then wordArrival b w else 0)*(1-countDecision b n (k-1)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      have heq : wordHeads w+1 = k ↔ wordHeads w = k-1 := by omega
      simp only [heq]
      split_ifs with hw <;> simp [hw]
    rw [htrue]
    ring
  · have hk0 : k = 0 := by omega
    simp [hk0]

theorem wordArrivalCount_eq_policyArrival {N : ℕ} (b : CountState N → Bool) (n k : ℕ) :
    wordArrivalCount b n k = policyArrival 1 (countDecision b) n k := by
  induction n generalizing k with
  | zero => exact wordArrivalCount_zero b k
  | succ n ih => simp only [wordArrivalCount_succ,policyArrival,ih]

end ThresholdHC.StoppingProgram
