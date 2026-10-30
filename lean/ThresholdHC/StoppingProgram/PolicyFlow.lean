import ThresholdHC.StoppingProgram.PolicyWeights

/-! Every count-state stopping policy with forced root continuation and cap
stopping defines a unit-root cone flow. -/

noncomputable section
namespace ThresholdHC.StoppingProgram

theorem policyArrival_nonneg (p : ℕ → ℕ → ℝ) (hp : ∀ n k, p n k ≤ 1) (n k : ℕ) :
    0 ≤ policyArrival 1 p n k := by
  induction n generalizing k with
  | zero => simp only [policyArrival]; split_ifs <;> norm_num
  | succ n ih =>
    rw [policyArrival]
    apply add_nonneg (mul_nonneg (ih _) (sub_nonneg.mpr (hp _ _)))
    split_ifs
    · exact mul_nonneg (ih _) (sub_nonneg.mpr (hp _ _))
    · exact le_rfl

def policyFlow (N : ℕ) (p : ℕ → ℕ → ℝ) : Flow N where
  stopWeight s := policyArrival 1 p s.1.val s.2.val*p s.1.val s.2.val/(s.1.val.choose s.2.val:ℝ)
  continueWeight s := policyArrival 1 p s.1.val s.2.val*(1-p s.1.val s.2.val)/(s.1.val.choose s.2.val:ℝ)
  outputWeight _ := 0
  momentWeight _ := 0

theorem raw_policyFlow_stop {N : ℕ} (p : ℕ → ℕ → ℝ) (n k : ℕ) (hn : n ≤ N) :
    rawArray (policyFlow N p).stopWeight n k = policyArrival 1 p n k*p n k := by
  by_cases hk : k ≤ n
  · have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    simp only [rawArray,arrayAt,hn,hk,dite_true,policyFlow]
    field_simp
  · rw [rawArray_outside _ n k (by omega),policyArrival_outside _ _ n k (by omega),zero_mul]

theorem raw_policyFlow_continue {N : ℕ} (p : ℕ → ℕ → ℝ) (n k : ℕ) (hn : n ≤ N) :
    rawArray (policyFlow N p).continueWeight n k = policyArrival 1 p n k*(1-p n k) := by
  by_cases hk : k ≤ n
  · have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    simp only [rawArray,arrayAt,hn,hk,dite_true,policyFlow]
    field_simp
  · rw [rawArray_outside _ n k (by omega),policyArrival_outside _ _ n k (by omega),zero_mul]

theorem policyFlow_intensity (N : ℕ) (p : ℕ → ℕ → ℝ) (hroot : p 0 0 = 0) :
    intensity (policyFlow N p) = 1 := by simp [intensity,policyFlow,rootState,policyArrival,hroot]

theorem policyFlow_cone {N : ℕ} (p : ℕ → ℕ → ℝ)
    (hp : ∀ n k, 0 ≤ p n k ∧ p n k ≤ 1) (hroot : p 0 0 = 0)
    (hterm : ∀ k, k ≤ N → p N k = 1) : FlowCone (policyFlow N p) := by
  constructor
  · intro s
    exact div_nonneg (mul_nonneg (policyArrival_nonneg p (fun n k => (hp n k).2) _ _) (hp _ _).1) (Nat.cast_nonneg _)
  · intro s
    exact div_nonneg (mul_nonneg (policyArrival_nonneg p (fun n k => (hp n k).2) _ _)
      (sub_nonneg.mpr (hp _ _).2)) (Nat.cast_nonneg _)
  · exact fun _ => le_rfl
  · simp [policyFlow,rootState,hroot]
  · rfl
  · rfl
  · intro s hs
    have ht := hterm s.2.val (by have h := s.2.isLt; omega)
    simp only [policyFlow,hs,ht,sub_self,mul_zero,zero_div]
  · intro s hs
    have hn : s.1.val ≤ N := by have h := s.1.isLt; omega
    have hk : s.2.val ≤ s.1.val := by have h := s.2.isLt; omega
    have hch : (s.1.val.choose s.2.val:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    apply mul_left_cancel₀ hch
    rw [mul_add,mul_add,← mul_assoc,choose_pascal_low _ _ hs]
    rw [← arrayAt_state (policyFlow N p).stopWeight s,
      ← arrayAt_state (policyFlow N p).continueWeight s]
    change rawArray (policyFlow N p).stopWeight s.1.val s.2.val+
      rawArray (policyFlow N p).continueWeight s.1.val s.2.val =
        rawArray (policyFlow N p).continueWeight (s.1.val-1) s.2.val+_
    rw [raw_policyFlow_stop p _ _ hn,raw_policyFlow_continue p _ _ hn,
      raw_policyFlow_continue p _ _ (by omega)]
    have he : s.1.val = (s.1.val-1)+1 := by omega
    have harr := policyArrival.eq_2 1 p s.2.val (s.1.val-1)
    rw [Nat.succ_eq_add_one,← he] at harr
    by_cases hk0 : 0 < s.2.val
    · rw [← mul_assoc,choose_pascal_high _ _ hs hk0]
      change _ = _+rawArray (policyFlow N p).continueWeight (s.1.val-1) (s.2.val-1)
      rw [raw_policyFlow_continue p _ _ (by omega)]
      rw [ite_eq_left hk0] at harr
      nlinarith [harr]
    · have hkz : s.2.val = 0 := by omega
      simp only [hkz,Nat.cast_zero,zero_div,mul_zero,zero_mul,add_zero]
      rw [ite_eq_right hk0,hkz] at harr
      nlinarith [harr]
  · intro s
    simp only [policyFlow,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]

end ThresholdHC.StoppingProgram
