import ThresholdHC.ContinuousObserved.Decode
import ThresholdHC.BlindUpper.BatchMachine

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.BlindUpper

theorem processHistory_succ (x : ProcessTape) (n : ℕ) :
    processHistory x (n + 1) = processHistory x n ++ (x n).toList := by
  unfold processHistory
  rw [List.ofFn_succ']
  cases hx : x n <;> simp [processPrefix,List.concat_eq_append,hx] <;> rfl

theorem decodeTape_history (g : List Bool → Bool → Bool) (x : ProcessTape) (n : ℕ) :
    processHistory (decodeTape g x) n = decode g (processHistory x n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [processHistory_succ,processHistory_succ,ih]
    cases hx : x n with
    | none => simp [decodeTape,hx]
    | some b => simp [decodeTape,hx,decode_append_singleton]

theorem decodeTape_work (g : List Bool → Bool → Bool) (x : ProcessTape) :
    totalProcessWork (decodeTape g x) = totalProcessWork x := by
  unfold totalProcessWork
  congr 1
  funext n
  congr 1
  rw [Proofs.workOf_eq_sum,Proofs.workOf_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [processPrefix,decodeTape_isSome]
  rfl

theorem measurable_decodeTape {R : Type} [MeasurableSpace R]
    (g : R → List Bool → Bool → Bool) (hg : ∀ xs b, Measurable (fun r => g r xs b)) :
    Measurable (fun z : R × ProcessTape => decodeTape (g z.1) z.2) := by
  apply Measurable.of_eval
  intro n
  have hm : Measurable (fun z : R × List Bool => decode (g z.1) z.2) :=
    measurable_from_prod_countable_left (fun xs => measurable_decode g hg xs)
  have hd : Measurable (fun z : R × ProcessTape => decode (g z.1) (processHistory z.2 n)) :=
    hm.comp (measurable_fst.prodMk ((measurable_processHistory_fixed n).comp measurable_snd))
  have hs (b : Option Bool) : Measurable
      (fun z : R × ProcessTape => b.map (fun a => g z.1 (decode (g z.1) (processHistory z.2 n)) a)) := by
    cases b with
    | none => exact measurable_const
    | some b =>
      have hb : Measurable (fun z : R × List Bool => g z.1 z.2 b) :=
        measurable_from_prod_countable_left (fun xs => hg xs b)
      exact (measurable_of_countable (fun c : Bool => some c)).comp
        (hb.comp (measurable_fst.prodMk hd))
  have hm : Measurable (fun z : Option Bool × (R × ProcessTape) =>
      z.1.map (fun a => g z.2.1 (decode (g z.2.1) (processHistory z.2.2 n)) a)) :=
    measurable_from_prod_countable_right hs
  have hi : Measurable (fun z : R × ProcessTape => (z.2 n,z)) :=
    ((measurable_pi_apply n).comp measurable_snd).prodMk measurable_id
  exact hm.comp hi

end ThresholdHC.ContinuousObserved
