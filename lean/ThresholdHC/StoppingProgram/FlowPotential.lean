import ThresholdHC.StoppingProgram.FlowConservation
import ThresholdHC.StoppingProgram.Bellman

/-! Bellman potentials bound every normalized count flow, including flows
obtained by randomizing over ordered histories. Attainment is separate. -/

noncomputable section
open scoped BigOperators

namespace ThresholdHC.StoppingProgram

theorem rawArray_nonneg {N : ℕ} (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) (n k : ℕ) :
    0 ≤ rawArray u n k := by
  apply mul_nonneg (Nat.cast_nonneg _)
  unfold arrayAt
  split_ifs <;> first | exact hu _ | exact le_rfl

def rawFlowScore {N : ℕ} (f : Flow N) (r w : ℕ → ℕ → ℝ) (κ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
    (rawArray f.stopWeight n k*r n k-κ*rawArray f.continueWeight n k*w n k)

theorem flow_potential_bound {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (r w v : ℕ → ℕ → ℝ) (κ : ℝ)
    (hr : ∀ n k, 0 < n → n ≤ N → k ≤ n → r n k ≤ v n k)
    (hc : ∀ n k, n < N → k ≤ n → v (n+1) k+v (n+1) (k+1)-κ*w n k ≤ v n k) :
    rawFlowScore f r w κ ≤ intensity f*v 0 0 := by
  rw [← raw_weighted_telescope f hf v]
  unfold rawFlowScore rawLayer rawChildren
  apply Finset.sum_le_sum
  intro n hn
  have hnN : n ≤ N := by have h := Finset.mem_range.mp hn; omega
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
  have ha0 := rawArray_nonneg _ hf.stop_nonneg n k
  have hc0 := rawArray_nonneg _ hf.continue_nonneg n k
  have hstop : rawArray f.stopWeight n k*r n k ≤ rawArray f.stopWeight n k*v n k := by
    by_cases hn0 : n = 0
    · have hk0 : k = 0 := by omega
      subst n
      subst k
      have he : rawArray f.stopWeight 0 0 = 0 := by
        simp only [rawArray,Nat.choose_zero_right,Nat.cast_one,one_mul]
        change f.stopWeight (rootState N) = 0
        exact hf.root_stop
      rw [he,zero_mul,zero_mul]
    · exact mul_le_mul_of_nonneg_left (hr n k (by omega) hnN hkn) ha0
  have hcontinue : rawArray f.continueWeight n k*(v (n+1) k+v (n+1) (k+1)-κ*w n k) ≤
      rawArray f.continueWeight n k*v n k := by
    by_cases hnlt : n < N
    · exact mul_le_mul_of_nonneg_left (hc n k hnlt hkn) hc0
    · have he : n = N := by omega
      rw [he,rawArray_terminal f hf,zero_mul,zero_mul]
  nlinarith

def forcedBellman (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N n k : ℕ) : ℝ :=
  if n = 0 then rootBellman r w κ (N-1) else bellman r w κ (N-n) n k

theorem forcedBellman_stop (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N n k : ℕ) (hn : 0 < n) :
    r n k ≤ forcedBellman r w κ N n k := by
  rw [forcedBellman,ite_eq_right (by omega)]
  cases N-n with
  | zero => exact le_rfl
  | succ d => exact le_max_left _ _

theorem forcedBellman_continue (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N n k : ℕ)
    (hroot : w 0 0 = 1) (hn : n < N) (hk : k ≤ n) :
    forcedBellman r w κ N (n+1) k+forcedBellman r w κ N (n+1) (k+1)-κ*w n k ≤
      forcedBellman r w κ N n k := by
  by_cases hn0 : n = 0
  · have hk0 : k = 0 := by omega
    subst n
    subst k
    simp [forcedBellman,rootBellman,hroot]
  · simp only [forcedBellman,show n+1 ≠ 0 by omega,ite_false,hn0]
    rw [show N-n = (N-(n+1))+1 by omega,bellman]
    exact le_max_right _ _

theorem flowScore_le_rootBellman {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (r w : ℕ → ℕ → ℝ) (κ : ℝ) (hroot : w 0 0 = 1) :
    rawFlowScore f r w κ ≤ intensity f*rootBellman r w κ (N-1) := by
  have h := flow_potential_bound f hf r w (forcedBellman r w κ N) κ
    (fun n k hn _ _ => forcedBellman_stop r w κ N n k hn)
    (fun n k hn hk => forcedBellman_continue r w κ N n k hroot hn hk)
  simpa only [forcedBellman,ite_true] using h

end ThresholdHC.StoppingProgram
