import ThresholdHC.PilotFeedback.ScheduledBounds
import ThresholdHC.PilotFeedback.ScheduledPolicy
import ThresholdHC.PilotFeedback.OrderedBayes

namespace ThresholdHC.PilotFeedback.Scheduled
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

/-- A committed batch with an arbitrary lower bound at its leaves. Each
continuation gets the full history and its updated likelihood vector. -/
private theorem batch (P : Plan) (X : List Bool → ℝ) (B : Schedule) (v : List Bool)
    (T : Weights → ℕ) (d n k : ℕ) (xs : List Bool) (w : Weights)
    (actions : ∀ ys : List Bool, ys.length<n →
      action P (xs++ys) = effective B v (k+ys.length))
    (ends : ∀ ys : List Bool, ys.length=n → ∀ u : Weights,
      (T u : ℝ)*denominator ≤ precision*value P X d (xs++ys) u) :
    (suffix T (modes B v n k) w : ℝ)*denominator ≤ precision*value P X (n+d) xs w := by
  induction n generalizing k xs w with
  | zero => simpa [modes,suffix] using ends [] rfl w
  | succ n ih =>
    have ac : action P xs = effective B v k := by simpa using actions [] (by simp)
    have child (b : Bool) := ih (k+1) (xs++[b]) (advance w (action P xs) b)
      (fun ys hy => by
        simpa [List.append_assoc,show k+1+ys.length=k+(ys.length+1) by omega] using
          actions (b::ys) (by simp; omega))
      (fun ys hy u => by simpa [List.append_assoc] using ends (b::ys) (by simp [hy]) u)
    rw [show n+1+d=n+d+1 by omega,split_value,mul_add]
    simpa only [modes,suffix,Nat.cast_add,add_mul,←ac] using add_le_add (child false) (child true)

private theorem first_action (P : Plan) (v ys : List Bool) (hv : v.length=18)
    (early : ys.length < P.split v) :
    action P (v++ys) = effective P.first v ys.length := by
  have take : (v++ys).take 18=v := by rw [←hv,List.take_left]
  simp [action,Ordered.action,take,List.length_append,hv,effective,Pilot.choice,frozen,early]

private theorem second_action (P : Plan) (v ys bs : List Bool) (hv : v.length=18)
    (split : ys.length=(P.split v).val) :
    action P ((v++ys)++bs) = effective (fun _ => P.second (v++ys)) v (ys.length+bs.length) := by
  have boundary_word : (v++(ys++bs)).take (18+ys.length) = v++ys := by
    rw [←List.append_assoc,←hv,←List.length_append,List.take_left]
  have boundary : 18+(P.split v).val=(v++ys).length := by simp [hv,split]
  have late : ¬ys.length+bs.length < (P.split v).val := by omega
  simp [action,Ordered.action,hv,effective,Pilot.choice,frozen,List.length_append,late,boundary,boundary_word]

theorem at_pilot (rows : ∀ j : Fin 19, Row j) (P : Plan) (X : List Bool → ℝ) (v : List Bool) (hv : v.length=18) :
    (pilotFloor (v.count true) : ℝ)*denominator ≤ precision*value P X 7 v (pilotWeights 18 (v.count true)) := by
  let j := v.count true
  let k := (P.split v).val
  let w := pilotWeights 18 j
  have hk : k≤7 := Nat.le_of_lt_succ (P.split v).isLt
  have hj : j≤18 := List.count_le_length.trans hv.le
  have after (ys : List Bool) (len : ys.length=k) (u : Weights) :
      (tailCost j k u : ℝ)*denominator ≤ precision*value P X (7-k) (v++ys) u := by
    let B : Schedule := fun _ => P.second (v++ys)
    let ms := modes B v (7-k) k
    have c := tailCost_le j k u ms (mode_length ..)
      (by simpa only [Pilot.available,ite_true] using mode_count B v (7-k) k true)
      (by simpa only [Pilot.available,Bool.false_eq_true,ite_false] using mode_count B v (7-k) k false)
    apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr c : (tailCost j k u : ℝ) ≤ _) (Nat.cast_nonneg denominator)).trans
    apply batch P X B v leaf 0 (7-k) k
    · intro bs _
      simpa only [len] using second_action P v ys bs hv len
    · intro bs _ a
      exact Ordered.leaf_bound P.first X _ a
  let ms := modes P.first v k 0
  let h := ms.count (some true)
  let t := ms.count (some false)
  have perm := counts_perm ms
  have len := perm.length_eq
  simp only [canonical,List.length_append,List.length_replicate,mode_length,ms] at len
  have f : ms.count none = k-h-t := by dsimp [h,t,ms]; omega
  have ok : firstOK j k h t := by
    have H := mode_count P.first v k 0 true
    have T := mode_count P.first v k 0 false
    simp only [Pilot.available,ite_true,Bool.false_eq_true,ite_false,Nat.sub_zero] at H T
    exact ⟨H,T,by dsimp [h,t,ms]; omega⟩
  have ht' := ok.2.2
  have c := rows ⟨j,by omega⟩ (P.split v) ⟨h,by omega⟩ ⟨t,by omega⟩ ok
  change pilotFloor j ≤ suffix (tailCost j k) (canonical h t (k-h-t)) w at c
  have canon := suffix_perm (tailCost j k) perm w
  rw [f] at canon
  rw [←canon] at c
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr c : (pilotFloor j : ℝ) ≤ _) (Nat.cast_nonneg denominator)).trans
  have H := batch P X P.first v (tailCost j k) (7-k) k 0 v w
    (fun ys hy => by simpa using first_action P v ys hv hy) after
  simpa [show k+(7-k)=7 by omega,ms,w,j] using H

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

theorem bayes_lower (rows : ∀ j : Fin 19, Row j) (total : 186960371^2 * 10^6 ≤ pilotSum 18 0) (P : Plan) (X : List Bool → ℝ) :
    (186960371/1000000000 : ℝ)^2 ≤
      ∑ i, prior i * run P (prob i) (fun xs => (X xs - prob i)^2) 25 [] := by
  have h := pilot_bound rows P X 18 [] (by decide)
  have lo : (186960371:ℝ)^2 * (10^6:ℝ) ≤ (pilotSum 18 0 : ℝ) := by exact_mod_cast total
  norm_num only [List.count_nil,List.length_nil,zero_add,Nat.reduceAdd] at h
  simp only [value,pilotWeights,pow_zero,mul_one,Nat.sub_zero] at h
  simp only [Fin.sum_univ_succ,prior] at h ⊢
  norm_num [denominator,precision,radix] at h ⊢
  linarith only [h,lo]

end
end ThresholdHC.PilotFeedback.Scheduled
