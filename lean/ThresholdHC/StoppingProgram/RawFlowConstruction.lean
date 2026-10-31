import ThresholdHC.StoppingProgram.FlowConservation

/-! Binomial normalization turns arbitrary ordered-prefix mass conservation
into the paper's count-flow cone. -/

noncomputable section
namespace ThresholdHC.StoppingProgram

def normalizedRawFlow (N : ℕ) (a c : ℕ → ℕ → ℝ) : Flow N where
  stopWeight s := a s.1.val s.2.val/(s.1.val.choose s.2.val:ℝ)
  continueWeight s := c s.1.val s.2.val/(s.1.val.choose s.2.val:ℝ)
  outputWeight _ := 0
  momentWeight _ := 0

theorem raw_normalizedRawFlow_stop {N : ℕ} (a c : ℕ → ℕ → ℝ)
    (hout : ∀ n k, n < k → a n k = 0) (n k : ℕ) (hn : n ≤ N) :
    rawArray (normalizedRawFlow N a c).stopWeight n k = a n k := by
  by_cases hk : k ≤ n
  · have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    simp only [rawArray,arrayAt,hn,hk,dite_true,normalizedRawFlow]
    field_simp
  · rw [rawArray_outside _ n k (by omega),hout n k (by omega)]

theorem raw_normalizedRawFlow_continue {N : ℕ} (a c : ℕ → ℕ → ℝ)
    (hout : ∀ n k, n < k → c n k = 0) (n k : ℕ) (hn : n ≤ N) :
    rawArray (normalizedRawFlow N a c).continueWeight n k = c n k := by
  by_cases hk : k ≤ n
  · have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    simp only [rawArray,arrayAt,hn,hk,dite_true,normalizedRawFlow]
    field_simp
  · rw [rawArray_outside _ n k (by omega),hout n k (by omega)]

theorem normalizedRawFlow_intensity (N : ℕ) (a c : ℕ → ℕ → ℝ) :
    intensity (normalizedRawFlow N a c) = c 0 0 := by simp [intensity,normalizedRawFlow,rootState]

theorem normalizedRawFlow_cone (N : ℕ) (a c : ℕ → ℕ → ℝ)
    (ha : ∀ n k, 0 ≤ a n k) (hc : ∀ n k, 0 ≤ c n k)
    (haout : ∀ n k, n < k → a n k = 0) (hcout : ∀ n k, n < k → c n k = 0)
    (hroot : a 0 0 = 0) (hterm : ∀ k, k ≤ N → c N k = 0)
    (hrec : ∀ n k, n < N → k ≤ n+1 → a (n+1) k+c (n+1) k =
      c n k+(if 0 < k then c n (k-1) else 0)) : FlowCone (normalizedRawFlow N a c) := by
  constructor
  · exact fun s => div_nonneg (ha _ _) (Nat.cast_nonneg _)
  · exact fun s => div_nonneg (hc _ _) (Nat.cast_nonneg _)
  · exact fun _ => le_rfl
  · simp [normalizedRawFlow,rootState,hroot]
  · rfl
  · rfl
  · intro s hs
    have ht := hterm s.2.val (by have h := s.2.isLt; omega)
    simp only [normalizedRawFlow,hs,ht,zero_div]
  · intro s hs
    have hn : s.1.val ≤ N := by have h := s.1.isLt; omega
    have hk : s.2.val ≤ s.1.val := by have h := s.2.isLt; omega
    have hch : (s.1.val.choose s.2.val:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    apply mul_left_cancel₀ hch
    rw [mul_add,mul_add,← mul_assoc,choose_pascal_low _ _ hs]
    rw [← arrayAt_state (normalizedRawFlow N a c).stopWeight s,
      ← arrayAt_state (normalizedRawFlow N a c).continueWeight s]
    change rawArray (normalizedRawFlow N a c).stopWeight s.1.val s.2.val+
      rawArray (normalizedRawFlow N a c).continueWeight s.1.val s.2.val =
        rawArray (normalizedRawFlow N a c).continueWeight (s.1.val-1) s.2.val+_
    rw [raw_normalizedRawFlow_stop a c haout _ _ hn,raw_normalizedRawFlow_continue a c hcout _ _ hn,
      raw_normalizedRawFlow_continue a c hcout _ _ (by omega)]
    have harr := hrec (s.1.val-1) s.2.val (by omega) (by omega)
    rw [show s.1.val-1+1 = s.1.val by omega] at harr
    by_cases hk0 : 0 < s.2.val
    · rw [← mul_assoc,choose_pascal_high _ _ hs hk0]
      change _ = _+rawArray (normalizedRawFlow N a c).continueWeight (s.1.val-1) (s.2.val-1)
      rw [raw_normalizedRawFlow_continue a c hcout _ _ (by omega)]
      simpa only [ite_eq_left hk0] using harr
    · have hkz : s.2.val = 0 := by omega
      simp only [hkz,Nat.cast_zero,zero_div,mul_zero,zero_mul,add_zero]
      simpa only [hkz,lt_self_iff_false,ite_false,add_zero] using harr
  · intro s
    simp only [normalizedRawFlow,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]

end ThresholdHC.StoppingProgram
