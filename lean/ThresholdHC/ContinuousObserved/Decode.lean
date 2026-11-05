import ThresholdHC.ObservedState.Finite
import ThresholdHC.BlindUpper.BatchMachine

noncomputable section
open MeasureTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier3

/-- Transform successive observations using only the already transformed history. -/
def decode (g : List Bool → Bool → Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => g [] b :: decode (fun ys => g (g [] b :: ys)) bs

theorem decode_length (g : List Bool → Bool → Bool) (xs : List Bool) :
    (decode g xs).length = xs.length := by
  induction xs generalizing g with
  | nil => rfl
  | cons b bs ih => simp only [decode,List.length_cons,ih]

theorem decode_append (g : List Bool → Bool → Bool) (xs ys : List Bool) :
    decode g (xs ++ ys) =
      decode g xs ++ decode (fun zs => g (decode g xs ++ zs)) ys := by
  induction xs generalizing g with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append,decode,ih]

theorem decode_append_singleton (g : List Bool → Bool → Bool) (xs : List Bool) (b : Bool) :
    decode g (xs ++ [b]) = decode g xs ++ [g (decode g xs) b] := by
  rw [decode_append]
  simp only [decode,List.append_nil]

theorem measurable_decode {R : Type} [MeasurableSpace R]
    (g : R → List Bool → Bool → Bool) (hg : ∀ xs b, Measurable (fun r => g r xs b))
    (xs : List Bool) : Measurable (fun r => decode (g r) xs) := by
  induction xs generalizing g with
  | nil => exact measurable_const
  | cons b bs ih =>
    let f (c : Bool) (r : R) := c :: decode (fun ys => g r (c :: ys)) bs
    have hf (c : Bool) : Measurable (f c) :=
      (measurable_of_countable (fun ys : List Bool => c :: ys)).comp
        (ih (fun r ys => g r (c :: ys)) (fun ys a => hg (c :: ys) a))
    have hm : Measurable (fun z : Bool × R => f z.1 z.2) := measurable_from_prod_countable_right hf
    exact hm.comp ((hg [] b).prodMk measurable_id)

/-- Decode a stopped observation tape without changing which entries are paid. -/
def decodeTape (g : List Bool → Bool → Bool) (x : ProcessTape) : ProcessTape :=
  fun n => (x n).map (fun b => g (decode g (processHistory x n)) b)

theorem decodeTape_isSome (g : List Bool → Bool → Bool) (x : ProcessTape) (n : ℕ) :
    (decodeTape g x n).isSome = (x n).isSome := by
  simp only [decodeTape,Option.isSome_map]

end ThresholdHC.ContinuousObserved
