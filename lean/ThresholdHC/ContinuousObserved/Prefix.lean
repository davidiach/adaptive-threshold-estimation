import ThresholdHC.ContinuousObserved.Tape

noncomputable section
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.CriticalEntropy

def decodePrefix {n : ℕ} (g : List Bool → Bool → Bool) (w : Prefix n) : Prefix n :=
  fun i => (w i).map (fun b => g (decode g (histBefore w i)) b)

theorem decodePrefix_processPrefix (g : List Bool → Bool → Bool) (x : ProcessTape) (n : ℕ) :
    decodePrefix g (processPrefix n x) = processPrefix n (decodeTape g x) := by
  funext i
  rfl

theorem decodePrefix_none {n : ℕ} (g : List Bool → Bool → Bool) :
    decodePrefix g (fun _ : Fin n => none) = (fun _ => none) := by
  funext i
  rfl

theorem decodePrefix_cons_none {n : ℕ} (g : List Bool → Bool → Bool) (w : Prefix n) :
    decodePrefix g (Fin.cons none w) = Fin.cons none (decodePrefix g w) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · simp only [decodePrefix,Fin.cons_succ,histBefore_cons_succ,Option.toList_none,List.nil_append]

theorem decodePrefix_cons_some {n : ℕ} (g : List Bool → Bool → Bool) (w : Prefix n) (b : Bool) :
    decodePrefix g (Fin.cons (some b) w) =
      Fin.cons (some (g [] b)) (decodePrefix (fun ys => g (g [] b :: ys)) w) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [decodePrefix,Fin.cons_zero,histBefore_cons_zero,decode,Option.map_some]
  · simp only [decodePrefix,Fin.cons_succ,histBefore_cons_succ,Option.toList_some,
      List.singleton_append,decode]

end ThresholdHC.ContinuousObserved
