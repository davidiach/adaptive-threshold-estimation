import MultiBiasData
import LargeBudgetTranscript
import SharpWeakRisk

/-! Each symmetric sign pair controls a different logarithmic test under the
same fair transcript law. Only the expected work under that common law enters. -/
noncomputable section
namespace ThresholdHC.SharpRMS.MultiBias
open Real Proofs Tier3 Tier5 LargeBudget

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

theorem bias_lt (i : Fin 5) : |bias i|<1 := by
  rw [abs_of_pos (params i).1]
  nlinarith [(params i).2.1,sq_nonneg (bias i-1)]

theorem pair_prefix {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ) (hs : 0<s) (hs' : s<1)
    (i : Fin 5) (X : Prefix n → ℝ) :
    prefixExpect pol s 0 (fun w => pair i (X w)) ≤
      charge s (bias i)*prefixExpect (n:=n) pol s 0 workOf +
      slope i*(prefixExpect pol s (bias i) (fun w => (X w-bias i)^2) +
               prefixExpect pol s (-bias i) (fun w => (X w-(-bias i))^2)-2*target) := by
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
  have vp := valid (bias i) (bias_lt i)
  have vm := valid (-bias i) (by simpa using bias_lt i)
  have v0 := valid 0 (by norm_num)
  have atom (w : Prefix n) : P w*pair i (X w) ≤
      P w*(log (P w/Q (bias i) w)+log (P w/Q (-bias i) w))+
      slope i*(Q (bias i) w*(X w-bias i)^2+Q (-bias i) w*(X w-(-bias i))^2) +
      (1-slope i*target)*(Q (bias i) w+Q (-bias i) w)-2*P w := by
    have single (t : ℝ) (ht : |t|<1) := gibbs (P w) (Q t w) (test i t (X w)) (v0.1 w)
      ((valid t ht).1 w) (supp t ht w) (test_pos ..)
    unfold pair
    have h := single (bias i) (bias_lt i)
    have k := single (-bias i) (by simpa using bias_lt i)
    unfold test at h k ⊢
    linear_combination h+k
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => atom w)
  have p1 : ∑ w, P w=1 := v0.2
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,p1,vp.2,vm.2] at sum
  have cost := adaptive_reverse_cost (n:=n) pol s (bias i) hs hs' (params i).2.1
  change (∑ w, P w*(log (P w/Q (bias i) w)+log (P w/Q (-bias i) w))) ≤ charge s (bias i)*∑ w, P w*workOf w at cost
  unfold prefixExpect
  change (∑ w, P w*_) ≤ charge s (bias i)*(∑ w, P w*_) +
    slope i*((∑ w, Q (bias i) w*_)+(∑ w, Q (-bias i) w*_)-2*target)
  linear_combination sum+cost

end ThresholdHC.SharpRMS.MultiBias
