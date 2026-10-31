import ThresholdHC.StoppingProgram.FlowBasics

/-! The normalized Pascal flow is bounded by its root intensity; zero
intensity forces every stopping, continuation and output coordinate to zero. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.StoppingProgram

theorem state_eq_root {N : ℕ} (s : CountState N) (h : s.1.val = 0) : s = rootState N := by
  rcases s with ⟨⟨n,hn⟩,⟨k,hk⟩⟩
  change n = 0 at h
  subst n
  have hk0 : k = 0 := by change k < 0+1 at hk; omega
  subst k
  rfl

theorem arrayAt_le_of (N n k : ℕ) (u : CountState N → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ s, s.1.val = n → u s ≤ M) : arrayAt u n k ≤ M := by
  unfold arrayAt
  split_ifs with hn hk
  · exact hu _ rfl
  · exact hM
  · exact hM

theorem pascal_weights_sum (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    (((n-k:ℕ):ℝ)/n)+(k:ℝ)/n = 1 := by
  rw [← add_div, Nat.cast_sub hk]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem flow_total_le_intensity {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    f.stopWeight s+f.continueWeight s ≤ intensity f := by
  have hroot : 0 ≤ intensity f := hf.continue_nonneg (rootState N)
  suffices h : ∀ n, ∀ s : CountState N, s.1.val = n →
      f.stopWeight s+f.continueWeight s ≤ intensity f by exact h s.1.val s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hs
    by_cases hn : n = 0
    · have he := state_eq_root s (hs.trans hn)
      rw [he,hf.root_stop,zero_add]
      exact le_refl _
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hc (k : ℕ) : arrayAt f.continueWeight (n-1) k ≤ intensity f := by
      apply arrayAt_le_of N (n-1) k _ hroot
      intro t ht
      have h := ih (n-1) (by omega) t ht
      linarith [hf.stop_nonneg t]
    have hr := hf.recursion s (by omega)
    simp only [hs] at hr
    have h0 : 0 ≤ (((n-s.2.val:ℕ):ℝ)/n) := by positivity
    have h1 : 0 ≤ (s.2.val:ℝ)/n := by positivity
    have hsum := pascal_weights_sum n s.2.val hn' (by have h := s.2.isLt; omega)
    have h := add_le_add (mul_le_mul_of_nonneg_left (hc s.2.val) h0)
      (mul_le_mul_of_nonneg_left (hc (s.2.val-1)) h1)
    rw [← add_mul,hsum,one_mul] at h
    exact hr.le.trans h

theorem flow_stop_le_intensity {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    f.stopWeight s ≤ intensity f := by
  linarith [flow_total_le_intensity f hf s,hf.continue_nonneg s]

theorem flow_continue_le_intensity {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    f.continueWeight s ≤ intensity f := by
  linarith [flow_total_le_intensity f hf s,hf.stop_nonneg s]

theorem flow_output_zero_of_stop_zero {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (s : CountState N) (hs : f.stopWeight s = 0) : f.outputWeight s = 0 := by
  have h := hf.perspective s
  rw [hs,zero_mul] at h
  nlinarith [sq_nonneg (f.outputWeight s)]

theorem flow_zero_intensity {N : ℕ} (f : Flow N) (hf : FlowCone f) (hroot : intensity f = 0)
    (s : CountState N) : f.stopWeight s = 0 ∧ f.continueWeight s = 0 ∧ f.outputWeight s = 0 := by
  have hs := le_antisymm ((flow_stop_le_intensity f hf s).trans_eq hroot) (hf.stop_nonneg s)
  have hc := le_antisymm ((flow_continue_le_intensity f hf s).trans_eq hroot) (hf.continue_nonneg s)
  exact ⟨hs,hc,flow_output_zero_of_stop_zero f hf s hs⟩

end ThresholdHC.StoppingProgram
