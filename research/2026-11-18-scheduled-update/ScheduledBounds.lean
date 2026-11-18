import OrderedCounts

/-! Each first-batch outcome gets its own minimum over legal second batches.
All allocations use the absolute follow-up position in the original menu. -/
namespace PilotFeedback.Scheduled
open Ordered

def minThrough (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n+1 => min (minThrough f n) (f (n+1))

theorem minThrough_le (f : ℕ → ℕ) {a n : ℕ} (h : a≤n) : minThrough f n ≤ f a := by
  induction n with
  | zero => obtain rfl := Nat.eq_zero_of_le_zero h; rfl
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with lt | rfl
    · exact (min_le_left ..).trans (ih (by omega))
    · exact min_le_right ..

def tailCost (j k : ℕ) (w : Weights) :=
  minThrough (fun h => minThrough (fun t => suffix leaf (canonical h t (7-k-h-t)) w)
    (min (7-k-h) (18-j-k))) (min (7-k) (j-k))

theorem tailCost_le (j k : ℕ) (w : Weights) (ms : List Mode)
    (hl : ms.length=7-k) (hh : ms.count (some true) ≤ j-k)
    (ht : ms.count (some false) ≤ 18-j-k) : tailCost j k w ≤ suffix leaf ms w := by
  let h := ms.count (some true)
  let t := ms.count (some false)
  have perm := counts_perm ms
  have len := perm.length_eq
  simp only [canonical,List.length_append,List.length_replicate,hl] at len
  have f : ms.count none=7-k-h-t := by dsimp [h,t]; omega
  rw [suffix_perm leaf perm,f]
  unfold tailCost
  apply (minThrough_le _ (a := h) (n := min (7-k) (j-k)) (le_min (by dsimp [h]; omega) hh)).trans
  exact minThrough_le _ (a := t) (n := min (7-k-h) (18-j-k)) (le_min (by dsimp [t,h]; omega) ht)

/-- Per ordered pilot word in units of 1e-24. The finite proof below checks the
displayed lower bounds independently of how the candidate values were found. -/
def pilotFloor (j : ℕ) : ℕ :=
  [140427895077,97434502523,66203927415,44132571187,29282137853,19988901380,
   14748829617,12246730114,11448451718,11283693776,11448451718,12246730114,
   14748829617,19988901380,29282137853,44132571187,66203927415,97434502523,
   140427895077][j]?.getD 0 * 10^7

def firstOK (j k h t : ℕ) : Prop :=
  h≤j ∧ t≤18-j ∧ h+t≤k

instance (j k h t : ℕ) : Decidable (firstOK j k h t) := by
  unfold firstOK
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def Row (j : ℕ) := ∀ (k h t : Fin 8), firstOK j k h t →
  pilotFloor j ≤ suffix (tailCost j k) (canonical h t (k-h-t)) (pilotWeights 18 j)

instance (j : ℕ) : Decidable (Row j) := by
  unfold Row
  infer_instance

def pilotSum : ℕ → ℕ → ℕ
  | 0, j => pilotFloor j
  | n+1, j => pilotSum n j + pilotSum n (j+1)

end PilotFeedback.Scheduled
