import ThresholdHC.LargeBudgetRMS.LargeBudgetTest
import ThresholdHC.LargeBudgetRMS.LargeBudgetTranscript
import ThresholdHC.SharpRMS.WeakRisk

/-! Passing a pointwise test to the three risks costs only the fair-law work. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open Real Tier3 Tier5 Proofs

private theorem gibbs (p q a : ℝ) (hp : 0≤p) (hq : 0≤q) (ac : p≠0 → q≠0) (ha : 0<a) :
    p*log a ≤ p*log (p/q)+q*a-p := by
  by_cases hz : p=0
  · simp [hz,mul_nonneg hq ha.le]
  have pp := lt_of_le_of_ne hp (Ne.symm hz)
  have qp := lt_of_le_of_ne hq (Ne.symm (ac hz))
  have h := log_le_sub_one_of_pos (div_pos (mul_pos qp ha) pp)
  rw [log_div (mul_pos qp ha).ne' hz,log_mul qp.ne' ha.ne'] at h
  rw [log_div hz qp.ne']
  have hh := mul_le_mul_of_nonneg_right h hp
  field_simp [hz] at hh
  linarith

theorem prefix_test {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ)
    (hs : 0<s) (hs' : s<1) (X : Prefix n → ℝ) (hx : ∀ w, |X w|≤1) :
    floorLog+2*(1-intercept) ≤ tilt*prefixExpect pol s 0 (fun w => (X w)^2) +
      weight*prefixExpect pol s bias (fun w => (X w-bias)^2) +
      weight*prefixExpect pol s (-bias) (fun w => (X w+bias)^2) +
      charge s bias*prefixExpect (n:=n) pol s 0 workOf := by
  let Q := fun t : ℝ => creationLaw (n:=n) pol (fun _ => s/2) (fun _ => (1+t)/2)
  let P := Q 0
  have valid (t : ℝ) (ht : |t|<1) : (∀ w, 0≤Q t w) ∧ ∑ w, Q t w=1 :=
    creationLaw_total _ pol _ _ (fun _ => ⟨by linarith,by linarith⟩)
      (fun _ => ⟨by linarith [(abs_lt.mp ht).1],by linarith [(abs_lt.mp ht).2]⟩)
  have supp (t : ℝ) (ht : |t|<1) (w : Prefix n) : P w≠0 → Q t w≠0 := by
    intro p z
    have e (v : ℝ) (hv : |v|<1) := transcriptLaw_zero_iff (capPolicy (coinCap n pol) pol)
      (fun _ => s/2) (fun _ => (1+v)/2) (fun _ => ⟨by linarith,by linarith⟩)
      (fun _ => ⟨by linarith [(abs_lt.mp hv).1],by linarith [(abs_lt.mp hv).2]⟩) w
    exact p ((e 0 (by norm_num)).2 ((e t ht).1 z))
  have v0 := valid 0 (by norm_num)
  have vp := valid bias (by norm_num)
  have vm := valid (-bias) (by norm_num)
  have per (w : Prefix n) : P w*(floorLog+2) ≤
      tilt*(P w*(X w)^2)+weight*(Q bias w*(X w-bias)^2)+weight*(Q (-bias) w*(X w+bias)^2)+
      P w*(log (P w/Q bias w)+log (P w/Q (-bias) w))+intercept*(Q bias w+Q (-bias) w) := by
    have h := mul_le_mul_of_nonneg_left (log_tests (X w) (hx w)) (v0.1 w)
    have hp := gibbs (P w) (Q bias w) (testValue bias (X w)) (v0.1 w) (vp.1 w)
      (supp bias (by norm_num) w) (testValue_pos ..)
    have hm := gibbs (P w) (Q (-bias) w) (testValue (-bias) (X w)) (v0.1 w) (vm.1 w)
      (supp (-bias) (by norm_num) w) (testValue_pos ..)
    change P w*floorLog ≤ P w*_ at h
    unfold testValue at hp hm h
    rw [sub_neg_eq_add] at hm h
    linear_combination h + hp + hm
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => per w)
  have p1 : ∑ w, P w=1 := v0.2
  simp only [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,p1,vp.2,vm.2] at sum
  have cost := adaptive_reverse_cost (n:=n) pol s bias hs hs' (by norm_num)
  change (∑ w, P w*(log (P w/Q bias w)+log (P w/Q (-bias) w))) ≤ charge s bias*∑ w, P w*workOf w at cost
  unfold prefixExpect
  change _ ≤ tilt*(∑ w, P w*_) + weight*(∑ w, Q bias w*_) + weight*(∑ w, Q (-bias) w*_) +
    charge s bias*(∑ w, P w*_)
  linear_combination sum + cost

end ThresholdHC.SharpRMS.LargeBudget
