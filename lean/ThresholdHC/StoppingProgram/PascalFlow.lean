import ThresholdHC.StoppingProgram.FlowBounds

/-! Binomial unnormalization of the count-state flow. The resulting raw
weights satisfy the ordinary binary-prefix conservation equation. -/

noncomputable section
open scoped BigOperators

namespace ThresholdHC.StoppingProgram

def rawArray {N : ℕ} (u : CountState N → ℝ) (n k : ℕ) : ℝ :=
  (n.choose k:ℝ)*arrayAt u n k

theorem choose_pascal_low (n k : ℕ) (hn : 0 < n) :
    (n.choose k:ℝ)*(((n-k:ℕ):ℝ)/n) = ((n-1).choose k:ℝ) := by
  have he : n-1+1 = n := by omega
  have h := Nat.choose_mul_succ_eq (n-1) k
  rw [he] at h
  have h' : (((n-1).choose k:ℕ):ℝ)*(n:ℝ) = (n.choose k:ℝ)*((n-k:ℕ):ℝ) := by exact_mod_cast h
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_div_assoc,div_eq_iff hn0]
  exact h'.symm

theorem choose_pascal_high (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (n.choose k:ℝ)*((k:ℝ)/n) = ((n-1).choose (k-1):ℝ) := by
  have h := Nat.add_one_mul_choose_eq (n-1) (k-1)
  rw [show n-1+1 = n by omega,show k-1+1 = k by omega] at h
  have h' : (n:ℝ)*((n-1).choose (k-1):ℝ) = (n.choose k:ℝ)*(k:ℝ) := by exact_mod_cast h
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_div_assoc,div_eq_iff hn0]
  nlinarith

theorem arrayAt_state {N : ℕ} (u : CountState N → ℝ) (s : CountState N) :
    arrayAt u s.1.val s.2.val = u s := by
  simp only [arrayAt,show s.1.val ≤ N by have h := s.1.isLt; omega,
    show s.2.val ≤ s.1.val by have h := s.2.isLt; omega,dite_true]

theorem raw_flow_recursion {N : ℕ} (f : Flow N) (hf : FlowCone f) (n k : ℕ)
    (hn : 0 < n) (hN : n ≤ N) (hk : k ≤ n) :
    rawArray f.stopWeight n k+rawArray f.continueWeight n k =
      rawArray f.continueWeight (n-1) k+
        (if 0 < k then rawArray f.continueWeight (n-1) (k-1) else 0) := by
  let s : CountState N := ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩
  have hr := congrArg (fun x : ℝ => (n.choose k:ℝ)*x) (hf.recursion s hn)
  change (n.choose k:ℝ)*(f.stopWeight s+f.continueWeight s) =
    (n.choose k:ℝ)*((((n-k:ℕ):ℝ)/n)*arrayAt f.continueWeight (n-1) k+
      (k:ℝ)/n*arrayAt f.continueWeight (n-1) (k-1)) at hr
  unfold rawArray
  rw [show arrayAt f.stopWeight n k = f.stopWeight s from arrayAt_state _ s,
    show arrayAt f.continueWeight n k = f.continueWeight s from arrayAt_state _ s,
    ← mul_add,hr,mul_add,← mul_assoc,choose_pascal_low n k hn]
  by_cases hk0 : 0 < k
  · rw [ite_eq_left hk0,← mul_assoc,choose_pascal_high n k hn hk0]
  · have he : k = 0 := by omega
    simp [he]

end ThresholdHC.StoppingProgram
