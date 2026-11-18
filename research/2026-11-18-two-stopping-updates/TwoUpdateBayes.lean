import TwoUpdatePolicy
import TwoUpdateBellman

namespace PilotFeedback.TwoUpdates
noncomputable section
open Ordered ThresholdHC.SharpRMS ThresholdHC.SharpRMS.Revisit

def value (P : Plan) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) (w : Weights) : ℝ :=
  (radix:ℝ)^n * ∑ i, (w i : ℝ) * run P (prob i) (fun ys => (X ys-prob i)^2) n xs

private theorem split_value (P : Plan) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) (w : Weights) :
    value P X (n+1) xs w =
      value P X n (xs++[false]) (advance w (action P xs) false) +
      value P X n (xs++[true]) (advance w (action P xs) true) := by
  simp only [value,run,advance,Nat.cast_mul,pow_succ,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [(code_prob _ _).1,(code_prob _ _).2]
  ring

def charge : Stage → Costs → ℕ
  | .initial, x => x.twice
  | .middle _, x => x.once
  | .final _ _, x => x.fixed

private theorem charge_add (s : Stage) (x y : Costs) :
    charge s (x.add y) = charge s x + charge s y := by cases s <;> rfl

private theorem current (P : Plan) (v xs : List Bool) (k : ℕ)
    (hv : xs.take 18=v) (hl : xs.length=18+k) :
    action P xs = allow (v.count true) k (schedule P v (update P (before P xs xs.length) xs) k) := by
  unfold action Ordered.action
  split
  · omega
  simp only [hv,hl,Nat.add_sub_cancel_left]
  unfold effective Pilot.choice frozen
  rw [←hl,List.take_length]
  cases e : schedule P v (update P (before P xs xs.length) xs) k with
  | none => rfl
  | some b => cases b <;> simp [allow,Pilot.available]

private theorem update_le (P : Plan) (xs v : List Bool) (s : Stage) (k : ℕ) (t : Table n) :
    charge s (lookup (cap (least t) t) (schedule P v s) k) ≤
      charge (update P s xs) (lookup t (schedule P v (update P s xs)) k) := by
  rw [lookup_cap]
  by_cases early : xs.length<18
  · cases s <;> simp [update,early,charge]
  · cases s with
    | initial =>
      cases h : P.trigger₁ xs <;> simp only [update,early,h,↓reduceIte,Bool.false_eq_true,charge]
      · exact min_le_left ..
      · exact (min_le_right ..).trans (least_le t _ k).2.1
    | middle z =>
      cases h : P.trigger₂ z xs <;> simp only [update,early,h,↓reduceIte,Bool.false_eq_true,charge]
      · exact min_le_left ..
      · exact (min_le_right ..).trans (least_le t _ k).1
    | final => simp [update,early,charge]

/-- At both answer children the next prescribed suffix comes from the very
same schedule. Each child can nevertheless make its own next trigger decision. -/
private theorem follow (P : Plan) (X : List Bool → ℝ) (v : List Bool) (n k : ℕ)
    (xs : List Bool) (w : Weights) (hv : xs.take 18=v) (hl : xs.length=18+k) :
    (charge (before P xs xs.length) (lookup (solve (v.count true) n k w)
      (schedule P v (before P xs xs.length)) k) : ℝ)*denominator ≤ precision*value P X n xs w := by
  induction n generalizing xs w k with
  | zero =>
    cases before P xs xs.length <;> exact leaf_bound P.first X xs w
  | succ n ih =>
    let s := before P xs xs.length
    let z := update P s xs
    let next := fun m b => solve (v.count true) n (k+1) (advance w m b)
    let t := candidates (v.count true) k next
    have child (b : Bool) := ih (k+1) (xs++[b]) (advance w (action P xs) b)
      (by rw [List.take_append_of_le_length (by omega),hv]) (by simp [hl,Nat.add_assoc])
    simp only [before_snoc] at child
    change (charge s (lookup (cap (least t) t) (schedule P v s) k) : ℝ)*denominator ≤ _
    apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (update_le P xs v s k t))
      (Nat.cast_nonneg denominator)).trans
    change (charge z (lookup (candidates _ _ next) (schedule P v z) k) : ℝ)*denominator ≤ _
    rw [lookup_candidates,charge_add,Nat.cast_add,add_mul,split_value,mul_add]
    have ac : action P xs = allow (v.count true) k (schedule P v z k) := current P v xs k hv hl
    simpa only [next,←ac,z,s] using add_le_add (child false) (child true)

theorem at_pilot (rows : ∀ j : Fin 19, Row j) (P : Plan) (X : List Bool → ℝ)
    (v : List Bool) (hv : v.length=18) :
    (floorRow (v.count true) : ℝ)*denominator ≤ precision*value P X 7 v (pilotWeights 18 (v.count true)) := by
  have hj : v.count true ≤ 18 := List.count_le_length.trans hv.le
  have c := (rows ⟨v.count true,by omega⟩).trans
    (least_le (solve (v.count true) 7 0 (pilotWeights 18 (v.count true))) (P.first v) 0).2.2
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr c) (Nat.cast_nonneg denominator)).trans
  have h := follow P X v 7 0 v (pilotWeights 18 (v.count true)) (by rw [←hv,List.take_length]) (by omega)
  simpa only [pilot_stage P v _ (by omega : v.length≤18),charge,schedule] using h

private theorem pilot_bound (rows : ∀ j : Fin 19, Row j) (P : Plan) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) (len : xs.length+n=18) :
    (pilotSum n (xs.count true) : ℝ)*denominator ≤
      precision*value P X (n+7) xs (pilotWeights xs.length (xs.count true)) := by
  induction n generalizing xs with
  | zero => simpa [pilotSum,show xs.length=18 by omega] using at_pilot rows P X xs (by omega)
  | succ n ih =>
    have ac : action P xs=none := by simp [action,Ordered.action,show xs.length<18 by omega]
    have child (b : Bool) := ih (xs++[b]) (by simp; omega)
    have step (b : Bool) : pilotWeights (xs++[b]).length ((xs++[b]).count true) =
        advance (pilotWeights xs.length (xs.count true)) (action P xs) b := by
      rw [ac,advance_pilot _ _ List.count_le_length]
      cases b <;> simp
    simp_rw [step] at child
    rw [show n+1+7=n+7+1 by omega,split_value,mul_add]
    simp only [pilotSum,Nat.cast_add,add_mul]
    simpa using add_le_add (child false) (child true)

theorem bayes_lower (rows : ∀ j : Fin 19, Row j) (total : 186764460^2 * 10^6 ≤ pilotSum 18 0) (P : Plan) (X : List Bool → ℝ) :
    (186764460/1000000000 : ℝ)^2 ≤
      ∑ i, prior i * run P (prob i) (fun xs => (X xs - prob i)^2) 25 [] := by
  have h := pilot_bound rows P X 18 [] (by decide)
  have lo : (186764460:ℝ)^2 * (10^6:ℝ) ≤ (pilotSum 18 0 : ℝ) := by exact_mod_cast total
  norm_num only [List.count_nil,List.length_nil,zero_add,Nat.reduceAdd] at h
  simp only [value,pilotWeights,pow_zero,mul_one,Nat.sub_zero] at h
  simp only [Fin.sum_univ_succ,prior] at h ⊢
  norm_num [denominator,precision,radix] at h ⊢
  linarith only [h,lo]

end
end PilotFeedback.TwoUpdates
