import ThresholdHC.StoppingUpdate.StoppingPolicy
import ThresholdHC.StoppingUpdate.StoppingBounds
import ThresholdHC.PilotFeedback.OrderedBayes

/-! The finite recursion bounds the Bayes loss of every stopping rule and
terminal estimate. Copied from the research module
`research/2026-11-18-stopping-update/StoppingBayes.lean`, preceded by the
lemma `modes_mem` of the research module `StoppingBounds.lean`. -/
namespace ThresholdHC.StoppingUpdate
noncomputable section
open ThresholdHC.PilotFeedback ThresholdHC.PilotFeedback.Ordered
open ThresholdHC.SharpRMS ThresholdHC.SharpRMS.Revisit

theorem modes_mem (B : Schedule) (v : List Bool) (n k : ℕ) :
    modes B v n k ∈ plans (v.count true) n k := by
  induction n generalizing k with
  | zero => simp [modes,plans]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨effective B v k, ?_, List.mem_map.mpr ⟨_, ih (k+1), rfl⟩⟩
    unfold effective Pilot.choice
    cases h : B v k with
    | none => simp [menu]
    | some b => cases b <;> simp [Pilot.available,menu] <;> omega

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

private theorem current (P : Plan) (v xs : List Bool) (k : ℕ)
    (hv : xs.take 18=v) (hl : xs.length=18+k) :
    action P xs = effective (match active P xs with
      | none => P.first
      | some z => fun _ => P.second z) v k := by
  unfold action Ordered.action
  split
  · omega
  simp only [hv,hl,Nat.add_sub_cancel_left]
  unfold effective Pilot.choice frozen active
  rw [←hl]
  cases boundary P xs xs.length <;> rfl

private theorem committed (P : Plan) (X : List Bool → ℝ) (B : Schedule) (v xs : List Bool)
    (k n : ℕ) (hn : n=7-k) (w : Weights)
    (acts : ∀ ys : List Bool, ys.length<n → action P (xs++ys) = effective B v (k+ys.length)) :
    (Scheduled.tailCost (v.count true) k w : ℝ)*denominator ≤ precision*value P X n xs w := by
  let ms := modes B v n k
  have c := Scheduled.tailCost_le (v.count true) k w ms ((mode_length ..).trans hn)
    (by simpa only [Pilot.available,ite_true] using mode_count B v n k true)
    (by simpa only [Pilot.available,Bool.false_eq_true,ite_false] using mode_count B v n k false)
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr c : (Scheduled.tailCost _ k w : ℝ) ≤ _)
    (Nat.cast_nonneg denominator)).trans
  exact batch P X B v leaf 0 n k xs w acts (fun _ _ u => Ordered.leaf_bound B X _ u)

private theorem unused_le_commit (j k : ℕ) (ms : List Mode) (w : Weights) :
    unused j ms k w ≤ Scheduled.tailCost j k w := by
  cases ms with
  | nil => rfl
  | cons m ms => exact min_le_left ..

/-- The two child histories may trigger at different times. Once triggered,
the chosen batch is fixed on every extension of that history. -/
private theorem follow (P : Plan) (X : List Bool → ℝ) (v : List Bool) (n k : ℕ)
    (xs : List Bool) (w : Weights) (hk : n+k=6) (hv : xs.take 18=v) (hl : xs.length=18+k) :
    (unused (v.count true) (modes P.first v n k) k w : ℝ)*denominator ≤
      precision*value P X (n+1) xs w := by
  induction n generalizing xs w k with
  | zero =>
    apply committed P X (match active P xs with
      | none => P.first
      | some z => fun _ => P.second z) v xs k 1 (by omega)
    intro ys hy
    have emp : ys=[] := List.length_eq_zero_iff.mp (by omega)
    subst ys
    simpa using current P v xs k hv hl
  | succ n ih =>
    have pilot (ys : List Bool) : (xs++ys).take 18=v := by
      rw [List.take_append_of_le_length (by omega),hv]
    cases ha : active P xs with
    | some z =>
      apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (unused_le_commit ..)) (Nat.cast_nonneg denominator)).trans
      apply committed P X (fun _ => P.second z) v xs k (n+1+1) (by omega)
      intro ys _
      have H := current P v (xs++ys) (k+ys.length) (pilot ys) (by simp [hl]; omega)
      rwa [active_append P xs ys z ha] at H
    | none =>
      have ac : action P xs=effective P.first v k := by simpa [ha] using current P v xs k hv hl
      have child (b : Bool) := ih (k+1) (xs++[b]) (advance w (action P xs) b) (by omega) (pilot [b])
        (by simp [hl,Nat.add_assoc])
      rw [modes,unused,split_value,mul_add]
      apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_right ..)) (Nat.cast_nonneg denominator)).trans
      simpa only [Nat.cast_add,add_mul,ac] using add_le_add (child false) (child true)

theorem at_pilot (rows : ∀ j : Fin 19, rowCheck j = true) (P : Plan) (X : List Bool → ℝ)
    (v : List Bool) (hv : v.length=18) :
    (floorRow (v.count true) : ℝ)*denominator ≤ precision*value P X 7 v (pilotWeights 18 (v.count true)) := by
  have hj : v.count true ≤ 18 := List.count_le_length.trans hv.le
  have H := List.all_eq_true.mp (rows ⟨v.count true,by omega⟩) _ (modes_mem P.first v 6 0)
  have c := of_decide_eq_true H
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr c) (Nat.cast_nonneg denominator)).trans
  exact follow P X v 6 0 v _ rfl (by rw [←hv,List.take_length]) (by omega)

private theorem pilot_bound (rows : ∀ j : Fin 19, rowCheck j = true) (P : Plan) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) (len : xs.length+n=18) :
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

theorem bayes_lower (rows : ∀ j : Fin 19, rowCheck j = true) (total : 186844275^2 * 10^6 ≤ pilotSum 18 0) (P : Plan) (X : List Bool → ℝ) :
    (186844275/1000000000 : ℝ)^2 ≤
      ∑ i, prior i * run P (prob i) (fun xs => (X xs - prob i)^2) 25 [] := by
  have h := pilot_bound rows P X 18 [] (by decide)
  have lo : (186844275:ℝ)^2 * (10^6:ℝ) ≤ (pilotSum 18 0 : ℝ) := by exact_mod_cast total
  norm_num only [List.count_nil,List.length_nil,zero_add,Nat.reduceAdd] at h
  simp only [value,pilotWeights,pow_zero,mul_one,Nat.sub_zero] at h
  simp only [Fin.sum_univ_succ,prior] at h ⊢
  norm_num [denominator,precision,radix] at h ⊢
  linarith only [h,lo]

end
end ThresholdHC.StoppingUpdate
