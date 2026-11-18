import ThresholdHC.LargeBudgetRMS.PilotPolicy
import ThresholdHC.LargeBudgetRMS.LargeBudgetBinomial

/-! The adaptive suffix is a binary tree indexed by the pilot head count.
The prefix sum therefore needs only nineteen binomial terms. -/
noncomputable section
namespace ThresholdHC.SharpRMS.Pilot
open Tier3 Tier5 Proofs LargeBudget Revisit

def tailAverage (A : Choices) (f : ℕ → ℕ → ℝ) (p : ℝ) (j : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, i => f j i
  | n+1, k, i =>
    let q := nextHead p (choice A j k i)
    (1-q)*tailAverage A f p j n (k+1) (2*i)+q*tailAverage A f p j n (k+1) (2*i+1)

def finish (A : Choices) (f : ℕ → ℕ → ℝ) (p : ℝ) (j : ℕ) := tailAverage A f p j 7 0 1

private def future (A : Choices) (f : ℕ → ℕ → ℝ) (p : ℝ) (xs : List Bool) : ℝ :=
  if xs.length<18 then binomialAverage (headProb p) (finish A f p) (18-xs.length) (xs.count true)
  else tailAverage A f p ((xs.take 18).count true) (25-xs.length) (xs.length-18) (index (xs.drop 18))

private theorem pilot_future (A : Choices) (f : ℕ → ℕ → ℝ) (p : ℝ) (xs : List Bool) (h : xs.length≤18) :
    future A f p xs = binomialAverage (headProb p) (finish A f p) (18-xs.length) (xs.count true) := by
  rcases lt_or_eq_of_le h with lt | eq
  · simp [future,lt]
  · simp [future,eq,List.take_of_length_le h,List.drop_eq_nil_of_le h,finish,binomialAverage,index]

private theorem future_step (A : Choices) (f : ℕ → ℕ → ℝ) (p : ℝ) (xs : List Bool) (hx : xs.length<25) :
    let r := nextHead p (action A xs)
    future A f p xs = (1-r)*future A f p (xs++[false])+r*future A f p (xs++[true]) := by
  by_cases h : xs.length<18
  · have hl (b : Bool) : (xs++[b]).length≤18 := by simp; omega
    rw [pilot_future _ _ _ _ h.le,pilot_future _ _ _ _ (hl false),pilot_future _ _ _ _ (hl true),
      show 18-xs.length=(18-(xs.length+1))+1 by omega]
    simp [action,h,nextHead,binomialAverage]
  · have ge : 18≤xs.length := by omega
    have hl : ¬xs.length+1<18 := by omega
    simp only [future,action,h,hl,ite_false,List.take_append_of_le_length ge,List.drop_append_of_le_length ge,
      List.length_append,List.length_singleton,index_append,Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    rw [show 25-xs.length=(25-(xs.length+1))+1 by omega,show xs.length+1-18=xs.length-18+1 by omega]
    rfl

theorem expect_counts (A : Choices) (f : ℕ → ℕ → ℝ) (p : ℝ) (hp : p∈Set.Icc 0 1) :
    (∑ w : Prefix 25, law (policy A) p w *
      f (((fullHist w).take 18).count true) (index ((fullHist w).drop 18))) =
      binomialAverage (headProb p) (finish A f p) 18 0 := by
  have H (n : ℕ) (hn : n≤25) :
      (∑ w : Prefix n, law (policy A) p w * future A f p (fullHist w))=
        binomialAverage (headProb p) (finish A f p) 18 0 := by
    induction n with
    | zero => simp [law,creationLaw,transcriptLaw_factor,pathValidity,coinLike,fullHist,future]
    | succ n ih =>
      rw [sum_snoc,←ih (by omega)]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hz : law (policy A) p w=0
      · have zero (o : Option Bool) : law (policy A) p (Fin.snoc w o)=0 := by
          have pos (a) : 0≤law (policy A) p (Fin.snoc w a) := (creationLaw_total _ (policy A) _ _ (fun _ => by norm_num) (fun _ => hp)).1 _
          have eq := creationLaw_sum_extensions (policy A) (fun _ => 1/5) (fun _ => p) w
          exact le_antisymm ((Finset.single_le_sum (fun a _ => pos a) (Finset.mem_univ o)).trans (eq.trans hz).le) (pos o)
        simp [zero,hz]
      obtain ⟨u,hu⟩ := valid_word (label A) (by omega) p hp w hz
      have st := future_step A f p (fullHist w) (by rw [hu,full_bits,List.length_ofFn]; omega)
      simp_rw [history_step A (by omega : n<25) p hp w hz]
      simp only [Fintype.sum_option,Fintype.sum_bool,obsProb,mul_zero,zero_mul,zero_add,fullHist_snoc_example,
        Option.toList_some]
      rw [st]; ring
  rw [←H 25 (by decide)]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hz : law (policy A) p w=0
  · simp [hz]
  obtain ⟨u,rfl⟩ := valid_word (label A) (by decide) p hp w hz
  simp [full_bits,future,tailAverage]

end ThresholdHC.SharpRMS.Pilot
