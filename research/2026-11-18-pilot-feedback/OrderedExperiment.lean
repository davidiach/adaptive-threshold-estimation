import OrderedPolicy

namespace PilotFeedback.Ordered
noncomputable section
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Proofs ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.Revisit

/-- Binary expectation with the whole ordered word passed to the output. -/
def run (A : Schedule) (p : ℝ) (X : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, xs => X xs
  | n+1, xs =>
    let r := nextHead p (action A xs)
    (1-r)*run A p X n (xs++[false]) + r*run A p X n (xs++[true])

theorem ordered_expect (A : Schedule) (p : ℝ) (hp : p∈Set.Icc 0 1) (X : List Bool → ℝ) :
    (∑ w : Prefix 25, law (policy A) p w * X (fullHist w)) = run A p X 25 [] := by
  have H (n : ℕ) (hn : n≤25) :
      (∑ w : Prefix n, law (policy A) p w * run A p X (25-n) (fullHist w)) = run A p X 25 [] := by
    induction n with
    | zero => simp [law,creationLaw,transcriptLaw_factor,pathValidity,coinLike,fullHist]
    | succ n ih =>
      rw [sum_snoc,←ih (by omega)]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hz : law (policy A) p w = 0
      · have zero (o : Option Bool) : law (policy A) p (Fin.snoc w o) = 0 := by
          have pos (a) : 0 ≤ law (policy A) p (Fin.snoc w a) :=
            (creationLaw_total _ (policy A) _ _ (fun _ => by norm_num) (fun _ => hp)).1 _
          have eq := creationLaw_sum_extensions (policy A) (fun _ => 1/5) (fun _ => p) w
          exact le_antisymm ((Finset.single_le_sum (fun a _ => pos a) (Finset.mem_univ o)).trans (eq.trans hz).le) (pos o)
        simp [zero,hz]
      simp_rw [history_step A (by omega : n<25) p hp w hz]
      rw [show 25-n=(25-(n+1))+1 by omega,run]
      simp only [Fintype.sum_option,Fintype.sum_bool,obsProb,mul_zero,zero_mul,zero_add,fullHist_snoc_example,
        Option.toList_some]
      ring
  exact H 25 (by decide)

end
end PilotFeedback.Ordered
