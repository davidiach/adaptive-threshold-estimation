import ThresholdHC.StoppingProgram.FlowBounds

/-! The deterministic policy which always takes exactly N observations is
an admissible unit-root normalized flow, including its boundary states. -/

noncomputable section
namespace ThresholdHC.StoppingProgram

def fullCapFlow (N : ℕ) : Flow N where
  stopWeight s := if s.1.val = N then 1 else 0
  continueWeight s := if s.1.val < N then 1 else 0
  outputWeight _ := 0
  momentWeight _ := 0

theorem fullCap_arrayAt {N n : ℕ} (hn : n < N) (k : ℕ) :
    arrayAt (fullCapFlow N).continueWeight n k = if k ≤ n then 1 else 0 := by
  unfold arrayAt
  simp only [show n ≤ N by omega, dite_true, fullCapFlow, hn, ite_true]
  split_ifs <;> rfl

theorem fullCapFlow_intensity {N : ℕ} (hN : 0 < N) : intensity (fullCapFlow N) = 1 := by
  simp only [intensity,fullCapFlow,rootState,hN,ite_true]

theorem fullCapFlow_cone {N : ℕ} (hN : 0 < N) : FlowCone (fullCapFlow N) := by
  constructor
  · intro s
    dsimp only [fullCapFlow]
    split_ifs <;> norm_num
  · intro s
    dsimp only [fullCapFlow]
    split_ifs <;> norm_num
  · exact fun _ => le_rfl
  · simp [fullCapFlow,rootState,show ¬0 = N by omega]
  · rfl
  · rfl
  · intro s hs
    simp only [fullCapFlow,hs,lt_self_iff_false,ite_false]
  · intro s hs
    have hn : s.1.val ≤ N := by have h := s.1.isLt; omega
    have hk : s.2.val ≤ s.1.val := by have h := s.2.isLt; omega
    rw [fullCap_arrayAt (by omega),fullCap_arrayAt (by omega)]
    have hkprev : s.2.val-1 ≤ s.1.val-1 := by omega
    rw [ite_eq_left hkprev,mul_one]
    have hlhs : (fullCapFlow N).stopWeight s+(fullCapFlow N).continueWeight s = 1 := by
      by_cases he : s.1.val = N
      · simp [fullCapFlow,he]
      · simp [fullCapFlow,he,show s.1.val < N by omega]
    rw [hlhs]
    by_cases hk' : s.2.val ≤ s.1.val-1
    · rw [ite_eq_left hk',mul_one]
      exact (pascal_weights_sum _ _ hs hk).symm
    · have he : s.2.val = s.1.val := by omega
      simp only [he,Nat.sub_self,Nat.cast_zero,zero_div,zero_mul,zero_add]
      exact (div_self (by exact_mod_cast hs.ne' : (s.1.val:ℝ) ≠ 0)).symm
  · intro s
    simp only [fullCapFlow,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]

end ThresholdHC.StoppingProgram
