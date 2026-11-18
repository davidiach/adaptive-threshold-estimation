import RevisitHistory
import LargeBudgetBinomial

noncomputable section
namespace ThresholdHC.SharpRMS.Revisit
open Tier3 Tier5 Proofs LargeBudget

def finish (f : ℕ → ℕ → ℝ) (p : ℝ) (j : ℕ) :=
  binomialAverage (nextHead p (mode j)) (f j) 5 0

private def future (f : ℕ → ℕ → ℝ) (p : ℝ) (xs : List Bool) : ℝ :=
  let j := (xs.take 20).count true
  if xs.length<20 then binomialAverage (headProb p) (finish f p) (20-xs.length) (xs.count true)
  else binomialAverage (nextHead p (mode j)) (f j) (25-xs.length) ((xs.drop 20).count true)

private theorem pilot_future (f : ℕ → ℕ → ℝ) (p : ℝ) (xs : List Bool) (h : xs.length≤20) :
    future f p xs = binomialAverage (headProb p) (finish f p) (20-xs.length) (xs.count true) := by
  rcases lt_or_eq_of_le h with lt | eq
  · simp [future,lt]
  · simp [future,eq,List.take_of_length_le h,List.drop_eq_nil_of_le h,finish,binomialAverage]

private theorem future_step (f : ℕ → ℕ → ℝ) (p : ℝ) (xs : List Bool) (hx : xs.length<25) :
    let r := nextHead p (if xs.length<20 then none else mode ((xs.take 20).count true))
    future f p xs = (1-r)*future f p (xs++[false])+r*future f p (xs++[true]) := by
  by_cases h : xs.length<20
  · have hl (b : Bool) : (xs++[b]).length≤20 := by simp; omega
    rw [pilot_future _ _ _ h.le,pilot_future _ _ _ (hl false),pilot_future _ _ _ (hl true),
      show 20-xs.length=(20-(xs.length+1))+1 by omega]
    simp [h,nextHead,binomialAverage]
  · have ge : 20≤xs.length := by omega
    have hl : ¬xs.length+1<20 := by omega
    simp only [future,h,hl,ite_false,List.take_append_of_le_length ge,List.drop_append_of_le_length ge,
      List.count_append,List.count_singleton,List.length_append,List.length_singleton]
    rw [show 25-xs.length=(25-(xs.length+1))+1 by omega]
    simp [binomialAverage]

/-- The exact two-stage experiment for any terminal function of the two head counts. -/
theorem expect_counts (f : ℕ → ℕ → ℝ) (p : ℝ) (hp : p∈Set.Icc 0 1) :
    (∑ w : Prefix 25, law policy p w * f (((fullHist w).take 20).count true) (((fullHist w).drop 20).count true)) =
      binomialAverage (headProb p) (finish f p) 20 0 := by
  have H (n : ℕ) (hn : n≤25) :
      (∑ w : Prefix n, law policy p w * future f p (fullHist w))=binomialAverage (headProb p) (finish f p) 20 0 := by
    induction n with
    | zero => simp [law,creationLaw,transcriptLaw_factor,pathValidity,coinLike,fullHist,future]
    | succ n ih =>
      rw [sum_snoc,←ih (by omega)]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hz : law policy p w=0
      · have zero (o : Option Bool) : law policy p (Fin.snoc w o)=0 := by
          have pos (a) : 0≤law policy p (Fin.snoc w a) := (creationLaw_total _ policy _ _ (fun _ => by norm_num) (fun _ => hp)).1 _
          have eq := creationLaw_sum_extensions policy (fun _ => 1/5) (fun _ => p) w
          exact le_antisymm ((Finset.single_le_sum (fun a _ => pos a) (Finset.mem_univ o)).trans (eq.trans hz).le) (pos o)
        simp [zero,hz]
      obtain ⟨u,hu⟩ := valid_word label (by omega) p hp w hz
      have len : (fullHist w).length=n := by rw [hu,full_bits,List.length_ofFn]
      have st := future_step f p (fullHist w) (by omega)
      simp_rw [history_step (by omega : n<25) p hp w hz]
      simp only [Fintype.sum_option,Fintype.sum_bool,obsProb,mul_zero,zero_mul,zero_add,fullHist_snoc_example,
        Option.toList_some]
      rw [len] at st
      rw [st]; ring
  rw [←H 25 (by decide)]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hz : law policy p w=0
  · simp [hz]
  obtain ⟨u,rfl⟩ := valid_word label (by decide) p hp w hz
  simp [full_bits,future,binomialAverage]

end ThresholdHC.SharpRMS.Revisit
