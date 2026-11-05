import ThresholdHC.LawAdaptation.Observation
import ThresholdHC.Anytime.Compatibility

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.BlindUpper
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

def pilotCost (n m : ℕ) : ℕ := 2*m*n

def pilotReader (m : ℕ) : ℕ → Reader
  | 0 => fun _ => 0
  | n+1 => thenRead (pilotCost n m) (pilotReader m n) (fun _ => n)

def coinWord (m : ℕ) (tape : ℕ → Bool) : List Bool :=
  List.ofFn (fun i : Fin (2*m) => tape i.val)

def wordParity (k : ℕ) (xs : List Bool) : ℝ :=
  parity (fun i : Fin (2*k) => xs[i.val]?.getD false)

def historySum (m k : ℕ) : ℕ → List Bool → ℝ
  | 0, _ => 0
  | n+1, xs => historySum m k n (xs.take (pilotCost n m)) +
      wordParity k (xs.drop (pilotCost n m))

def historyAverage (n m k : ℕ) (xs : List Bool) : ℝ := historySum m k n xs/(n:ℝ)

theorem readBlock_constant (n i : ℕ) (s : Table) :
    (readBlock n (fun _ => i) s).1 = List.ofFn (fun j : Fin n => s i j.val) := by
  induction n generalizing s with
  | zero => simp [readBlock]
  | succ n ih =>
    change s i 0 :: (readBlock n (fun _ => i) (Function.update s i (tapeDrop 1 (s i)))).1 = _
    rw [ih, List.ofFn_succ]
    simp only [Function.update_self, tapeDrop, Fin.val_zero, Fin.val_succ, Nat.add_comm]

theorem wordParity_coinWord (m k : ℕ) (hk : k ≤ m) (tape : ℕ → Bool) :
    wordParity k (coinWord m tape) = prefixParity k tape := by
  unfold wordParity prefixParity parity ThresholdHC.Tier2.tapePrefix
  apply Finset.prod_congr rfl
  intro i _
  have hi : i.val < 2*m := lt_of_lt_of_le i.isLt (Nat.mul_le_mul_left 2 hk)
  simp [coinWord, hi]

private theorem pilotReader_range (m n : ℕ) (hn : 0 < n) (xs : List Bool) :
    pilotReader m n xs < n := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    by_cases h : xs.length < pilotCost n m
    · have hn' : 0 < n := by
        by_contra he
        have hz : n=0 := by omega
        simp [hz,pilotCost] at h
      have hsmall := (ih hn' xs).trans (Nat.lt_succ_self n)
      simpa only [pilotReader,thenRead,ite_eq_left h] using hsmall
    · simp only [pilotReader,thenRead,ite_eq_right h]
      omega

theorem pilot_fresh (m n j : ℕ) (s : Table) (hj : n ≤ j) :
    (readBlock (pilotCost n m) (pilotReader m n) s).2 j = s j := by
  cases n with
  | zero => rfl
  | succ n =>
    apply readBlock_untouched
    intro xs he
    have h := pilotReader_range m (n+1) (Nat.zero_lt_succ _) xs
    omega

theorem pilot_word_succ (m n : ℕ) (s : Table) :
    (readBlock (pilotCost (n+1) m) (pilotReader m (n+1)) s).1 =
      (readBlock (pilotCost n m) (pilotReader m n) s).1 ++ coinWord m (s n) := by
  have hc : pilotCost (n+1) m = pilotCost n m + 2*m := by unfold pilotCost; ring
  rw [hc,pilotReader,readBlock_append]
  dsimp only
  rw [readBlock_constant,pilot_fresh m n n s le_rfl]
  rfl

/-- Every observed pilot coordinate equals the even-prefix statistic on the
original persistent coins, after exactly the stated number of physical flips. -/
theorem historySum_readBlock (m k n : ℕ) (hk : k ≤ m) (s : Table) :
    historySum m k n (readBlock (pilotCost n m) (pilotReader m n) s).1 =
      ∑ j : Fin n, prefixParity k (s j.val) := by
  induction n with
  | zero => simp [historySum]
  | succ n ih =>
    let w := (readBlock (pilotCost n m) (pilotReader m n) s).1
    have hlen : w.length = pilotCost n m := readBlock_length _ _ _
    have hword : (readBlock (pilotCost (n+1) m) (pilotReader m (n+1)) s).1 =
        w ++ coinWord m (s n) := pilot_word_succ m n s
    rw [historySum,hword,← hlen,List.take_left,List.drop_left,
      wordParity_coinWord m k hk,ih,Fin.sum_univ_castSucc]
    rfl

theorem historyAverage_readBlock (n m k : ℕ) (hk : k ≤ m) (s : Table) :
    historyAverage n m k (readBlock (pilotCost n m) (pilotReader m n) s).1 =
      pilotAverage n k s := by
  unfold historyAverage pilotAverage
  rw [historySum_readBlock m k n hk]

def chosenWord {ι : Type*} [Nonempty ι] (laws : ι → Measure Gap)
    (n m : ℕ) (η : ℝ) (xs : List Bool) : ι :=
  identify (fun i (k : Fin m) => evenMoment (laws i) (k.val+1))
    (fun k => historyAverage n m (k.val+1) xs) (η/4)

def chosenTable {ι : Type*} [Nonempty ι] (laws : ι → Measure Gap)
    (n m : ℕ) (η : ℝ) (s : Table) : ι :=
  identify (fun i (k : Fin m) => evenMoment (laws i) (k.val+1))
    (fun k => pilotAverage n (k.val+1) s) (η/4)

theorem chosenWord_readBlock {ι : Type*} [Nonempty ι] (laws : ι → Measure Gap)
    (n m : ℕ) (η : ℝ) (s : Table) :
    chosenWord laws n m η (readBlock (pilotCost n m) (pilotReader m n) s).1 =
      chosenTable laws n m η s := by
  unfold chosenWord chosenTable
  congr 1
  funext k
  exact historyAverage_readBlock n m (k.val+1) (by omega) s

end ThresholdHC.LawAdaptation

