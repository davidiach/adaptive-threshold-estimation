import ThresholdHC.Genie.FlowExtension

/-! Weighted flow conservation with extended nonnegative rewards. The
proofs use addition only and therefore remain valid at infinite rewards. -/

noncomputable section
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.StoppingProgram

def eRawLayer {N : ℕ} (u : CountState N → ℝ) (v : ℕ → ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (n+1), ENNReal.ofReal (rawArray u n k)*v n k

def eRawChildren {N : ℕ} (u : CountState N → ℝ) (v : ℕ → ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (n+1), ENNReal.ofReal (rawArray u n k)*(v (n+1) k+v (n+1) (k+1))

theorem rawArray_nonneg {N : ℕ} (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) (n k : ℕ) :
    0 ≤ rawArray u n k := mul_nonneg (Nat.cast_nonneg _) (arrayAt_nonneg u hu n k)

theorem eRaw_recursion {N : ℕ} (f : Flow N) (hf : FlowCone f) (n k : ℕ)
    (hn : 0 < n) (hN : n ≤ N) (hk : k ≤ n) :
    ENNReal.ofReal (rawArray f.stopWeight n k)+ENNReal.ofReal (rawArray f.continueWeight n k) =
      ENNReal.ofReal (rawArray f.continueWeight (n-1) k)+
        (if 0 < k then ENNReal.ofReal (rawArray f.continueWeight (n-1) (k-1)) else 0) := by
  rw [←ENNReal.ofReal_add (rawArray_nonneg _ hf.stop_nonneg _ _) (rawArray_nonneg _ hf.continue_nonneg _ _),
    raw_flow_recursion f hf n k hn hN hk]
  split_ifs
  · exact ENNReal.ofReal_add (rawArray_nonneg _ hf.continue_nonneg _ _) (rawArray_nonneg _ hf.continue_nonneg _ _)
  · simp

theorem eRaw_layer_conservation {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (v : ℕ → ℕ → ℝ≥0∞) (n : ℕ) (hn : n < N) :
    eRawLayer f.stopWeight v (n+1)+eRawLayer f.continueWeight v (n+1) =
      eRawChildren f.continueWeight v n := by
  unfold eRawLayer eRawChildren
  rw [←Finset.sum_add_distrib]
  have he : (∑ k ∈ Finset.range (n+1+1),
      (ENNReal.ofReal (rawArray f.stopWeight (n+1) k)*v (n+1) k+
        ENNReal.ofReal (rawArray f.continueWeight (n+1) k)*v (n+1) k)) =
      (∑ k ∈ Finset.range (n+2), ENNReal.ofReal (rawArray f.continueWeight n k)*v (n+1) k)+
      ∑ k ∈ Finset.range (n+2), (if 0 < k then ENNReal.ofReal (rawArray f.continueWeight n (k-1)) else 0)*v (n+1) k := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [←add_mul,eRaw_recursion f hf (n+1) k (by omega) (by omega)
      (by have h := Finset.mem_range.mp hk; omega)]
    simp only [Nat.add_sub_cancel,add_mul]
  rw [he]
  rw [Finset.sum_range_succ (fun k => ENNReal.ofReal (rawArray f.continueWeight n k)*v (n+1) k) (n+1),
    rawArray_outside _ n (n+1) (by omega),ENNReal.ofReal_zero,zero_mul,add_zero]
  rw [Finset.sum_range_succ' (fun k => (if 0 < k then ENNReal.ofReal (rawArray f.continueWeight n (k-1)) else 0)*v (n+1) k) (n+1)]
  simp only [Nat.succ_pos,ite_true,Nat.add_sub_cancel,lt_self_iff_false,ite_false,zero_mul,add_zero]
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by rw [mul_add])

theorem eRaw_terminal {N : ℕ} (f : Flow N) (hf : FlowCone f) (v : ℕ → ℕ → ℝ≥0∞) :
    eRawLayer f.continueWeight v N = 0 := by
  simp [eRawLayer,rawArray_terminal f hf]

theorem eRaw_harmonic_conservation {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (v : ℕ → ℕ → ℝ≥0∞) (hv : ∀ n k, k ≤ n → v (n+1) k+v (n+1) (k+1) = v n k)
    (n : ℕ) (hn : n < N) :
    eRawLayer f.stopWeight v (n+1)+eRawLayer f.continueWeight v (n+1) =
      eRawLayer f.continueWeight v n := by
  rw [eRaw_layer_conservation f hf v n hn]
  unfold eRawChildren eRawLayer
  apply Finset.sum_congr rfl
  intro k hk
  rw [hv n k (by have h := Finset.mem_range.mp hk; omega)]

theorem eRaw_tail_harmonic {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (v : ℕ → ℕ → ℝ≥0∞) (hv : ∀ n k, k ≤ n → v (n+1) k+v (n+1) (k+1) = v n k)
    (n len : ℕ) (hlen : n+len = N) :
    (∑ i ∈ Finset.range (len+1), eRawLayer f.stopWeight v (n+i)) =
      eRawLayer f.stopWeight v n+eRawLayer f.continueWeight v n := by
  induction len generalizing n with
  | zero =>
    have hn : n = N := by omega
    subst n
    simp [eRaw_terminal f hf]
  | succ len ih =>
    rw [Finset.sum_range_succ']
    have he : (∑ i ∈ Finset.range (len+1), eRawLayer f.stopWeight v (n+(i+1))) =
        ∑ i ∈ Finset.range (len+1), eRawLayer f.stopWeight v ((n+1)+i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [he,Nat.add_zero,ih (n+1) (by omega),eRaw_harmonic_conservation f hf v hv n (by omega)]
    exact add_comm _ _

theorem eRawLayer_mono {N : ℕ} (u : CountState N → ℝ) (v w : ℕ → ℕ → ℝ≥0∞)
    (n : ℕ) (h : ∀ k, k ≤ n → v n k ≤ w n k) : eRawLayer u v n ≤ eRawLayer u w n := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_right (h k (by have h := Finset.mem_range.mp hk; omega)) _

end ThresholdHC.Genie
