import OrderedCounts
import OrderedExperiment

namespace PilotFeedback.Ordered
noncomputable section
open ThresholdHC.SharpRMS ThresholdHC.SharpRMS.Revisit

def prob (i : Fin 4) : ℝ := (point i : ℝ)/10

theorem prob_mem (i : Fin 4) : prob i ∈ Set.Icc 0 1 := by
  fin_cases i <;> norm_num [prob,point]

theorem code_prob (m : Mode) (i : Fin 4) :
    (code m true i : ℝ) = radix * nextHead (prob i) m ∧
    (code m false i : ℝ) = radix * (1-nextHead (prob i) m) := by
  cases m with
  | none => fin_cases i <;> norm_num [code,headCode,radix,nextHead,headProb,prob,point]
  | some b => cases b <;> fin_cases i <;> norm_num [code,headCode,radix,nextHead,headProb,prob,point]

def value (A : Schedule) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) (w : Weights) : ℝ :=
  (radix:ℝ)^n * ∑ i, (w i : ℝ) * run A (prob i) (fun ys => (X ys-prob i)^2) n xs

theorem split_value (A : Schedule) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) (w : Weights) :
    value A X (n+1) xs w =
      value A X n (xs++[false]) (advance w (action A xs) false) +
      value A X n (xs++[true]) (advance w (action A xs) true) := by
  simp only [value, run,advance,Nat.cast_mul,pow_succ,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [(code_prob _ _).1,(code_prob _ _).2]
  ring

theorem leaf_bound (A : Schedule) (X : List Bool → ℝ) (xs : List Bool) (w : Weights) :
    (leaf w : ℝ)*denominator ≤ precision*value A X 0 xs w := by
  let s := w 0+w 1+w 2+w 3
  by_cases hz : s=0
  · have : w 0=0 ∧ w 1=0 ∧ w 2=0 ∧ w 3=0 := by dsimp [s] at hz; omega
    obtain ⟨a,b,c,d⟩ := this
    simp [leaf,value,Fin.sum_univ_succ,a,b,c,d]
  have pos : 0 < (w 0:ℝ)+w 1+w 2+w 3 := by exact_mod_cast Nat.pos_of_ne_zero hz
  have fl := Nat.div_mul_le_self (precision * pairSum (w 0) (w 1) (w 2) (w 3)) (100*denominator*s)
  change leaf w * (100*denominator*s) ≤ _ at fl
  have fr : (leaf w : ℝ) * (100*denominator*((w 0:ℝ)+w 1+w 2+w 3)) ≤
      precision * (pairSum (w 0) (w 1) (w 2) (w 3) : ℝ) := by exact_mod_cast fl
  have id : 100*((w 0:ℝ)+w 1+w 2+w 3)*value A X 0 xs w =
      (10*((w 0:ℝ)+w 1+w 2+w 3)*X xs-(3*w 1+7*w 2+10*w 3 : ℝ))^2 +
        (pairSum (w 0) (w 1) (w 2) (w 3) : ℝ) := by
    norm_num [value,Fin.sum_univ_succ,run,prob,point,pairSum]
    ring
  have bound : (pairSum (w 0) (w 1) (w 2) (w 3) : ℝ) ≤
      100*((w 0:ℝ)+w 1+w 2+w 3)*value A X 0 xs w := by
    rw [id]; linarith [sq_nonneg (10*((w 0:ℝ)+w 1+w 2+w 3)*X xs-(3*w 1+7*w 2+10*w 3 : ℝ))]
  have h := fr.trans (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg precision))
  apply le_of_mul_le_mul_left (a := 100*((w 0:ℝ)+w 1+w 2+w 3)) _ (by positivity)
  linarith only [h]

def modes (A : Schedule) (v : List Bool) : ℕ → ℕ → List Mode
  | 0, _ => []
  | n+1, k => effective A v k :: modes A v n (k+1)

theorem mode_length (A : Schedule) (v : List Bool) (n k : ℕ) : (modes A v n k).length=n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [modes,ih]

theorem mode_count (A : Schedule) (v : List Bool) (n k : ℕ) (b : Bool) :
    (modes A v n k).count (some b) ≤ Pilot.available (v.count true) b-k := by
  induction n generalizing k with
  | zero => simp [modes]
  | succ n ih =>
    have tail := ih (k+1)
    by_cases e : effective A v k = some b
    · have avail := Pilot.choice_available _ (show Pilot.choice (fun _ _ => A v k) (v.count true) k 0 = some b from e)
      simp [modes,e]
      omega
    · simpa [modes,List.count_cons,e] using (tail.trans (by omega : _ ≤ Pilot.available (v.count true) b-k))

private theorem suffix_bound (A : Schedule) (X : List Bool → ℝ) (v xs : List Bool)
    (ht : xs.take 18=v) (hg : 18≤xs.length) (n : ℕ) (w : Weights) :
    (suffix leaf (modes A v n (xs.length-18)) w : ℝ)*denominator ≤ precision*value A X n xs w := by
  induction n generalizing xs w with
  | zero => exact leaf_bound ..
  | succ n ih =>
    have ac : action A xs = effective A v (xs.length-18) := by simp [action,not_lt.mpr hg,ht]
    have child (b : Bool) := ih (xs++[b]) (by simpa [List.take_append_of_le_length hg] using ht)
      (by simp; omega) (advance w (action A xs) b)
    simp only [List.length_append,List.length_singleton,show xs.length+1-18=xs.length-18+1 by omega] at child
    rw [split_value,mul_add]
    simp only [modes,suffix,Nat.cast_add,add_mul,←ac]
    exact add_le_add (child false) (child true)

private theorem at_pilot (A : Schedule) (X : List Bool → ℝ) (v : List Bool) (hv : v.length=18) :
    (pilotBound (v.count true) : ℝ)*denominator ≤ precision*value A X 7 v (pilotWeights 18 (v.count true)) := by
  let j := v.count true
  let ms := modes A v 7 0
  let h := ms.count (some true)
  let t := ms.count (some false)
  have hj : j≤18 := (List.count_le_length).trans hv.le
  have hp := counts_perm ms
  have len := hp.length_eq
  simp [ms,canonical,mode_length] at len
  have hlen : h+t+ms.count none=7 := by dsimp [h,t,ms]; omega
  have legal' : legal j h t := by
    have H := mode_count A v 7 0 true
    have T := mode_count A v 7 0 false
    simp only [Pilot.available,ite_true,Bool.false_eq_true,ite_false,Nat.sub_zero] at H T
    exact ⟨H,T,by omega⟩
  have c := certified ⟨j,by omega⟩ ⟨h,by omega⟩ ⟨t,by omega⟩ legal'
  have eq : suffix leaf ms (pilotWeights 18 j) = suffix leaf (canonical h t (7-h-t)) (pilotWeights 18 j) := by
    rw [suffix_perm leaf hp]
    have : ms.count none=7-h-t := by omega
    rw [this]
  change pilotBound j ≤ suffix leaf (canonical h t (7-h-t)) (pilotWeights 18 j) at c
  rw [←eq] at c
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr c : (pilotBound j : ℝ) ≤ _) (Nat.cast_nonneg denominator)).trans
  simpa [ms,hv,j] using suffix_bound A X v v (by simp [←hv]) hv.ge 7 (pilotWeights 18 j)

theorem pilot_bound (A : Schedule) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) (len : xs.length+n=18) :
    (pilotTree n (xs.count true) : ℝ)*denominator ≤
      precision*value A X (n+7) xs (pilotWeights xs.length (xs.count true)) := by
  induction n generalizing xs with
  | zero => simpa [pilotTree,show xs.length=18 by omega] using at_pilot A X xs (by omega)
  | succ n ih =>
    have hg : xs.length<18 := by omega
    have ac : action A xs=none := by simp [action,hg]
    have child (b : Bool) := ih (xs++[b]) (by simp; omega)
    have step (b : Bool) : pilotWeights (xs++[b]).length ((xs++[b]).count true) =
        advance (pilotWeights xs.length (xs.count true)) (action A xs) b := by
      rw [ac,advance_pilot _ _ List.count_le_length]
      cases b <;> simp
    simp_rw [step] at child
    rw [show n+1+7=n+7+1 by omega,split_value,mul_add]
    simp only [pilotTree,Nat.cast_add,add_mul]
    simpa using add_le_add (child false) (child true)

theorem ordered_bayes (A : Schedule) (X : List Bool → ℝ) :
    (18735887/100000000 : ℝ)^2 ≤
      ∑ i, prior i * run A (prob i) (fun xs => (X xs - prob i)^2) 25 [] := by
  have h := pilot_bound A X 18 [] (by decide)
  have lo : (18735887:ℝ)^2 * (10^8:ℝ) ≤ (pilotTree 18 0 : ℝ) := by exact_mod_cast total
  norm_num only [List.count_nil,List.length_nil,zero_add,Nat.reduceAdd] at h
  simp only [value,pilotWeights,pow_zero,mul_one,Nat.sub_zero] at h
  simp only [Fin.sum_univ_succ,prior] at h ⊢
  norm_num [denominator,precision,radix] at h ⊢
  linarith only [h,lo]

end
end PilotFeedback.Ordered
