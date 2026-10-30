import ThresholdHC.StoppingProgram.PolicyFlow
import ThresholdHC.StoppingProgram.FlowPotential

/-! A deterministic count decision rule attains the Bellman upper bound over
the actual normalized flow cone. -/

noncomputable section
open scoped BigOperators Classical
namespace ThresholdHC.StoppingProgram

def bellmanStopProbability (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N n k : ℕ) : ℝ :=
  if n = 0 then 0 else if N ≤ n then 1 else
    if forcedBellman r w κ N (n+1) k+forcedBellman r w κ N (n+1) (k+1)-κ*w n k ≤ r n k
    then 1 else 0

theorem bellmanStopProbability_binary (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N n k : ℕ) :
    bellmanStopProbability r w κ N n k = 0 ∨ bellmanStopProbability r w κ N n k = 1 := by
  unfold bellmanStopProbability
  split_ifs <;> simp

theorem bellmanStopProbability_root (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N : ℕ) :
    bellmanStopProbability r w κ N 0 0 = 0 := by simp [bellmanStopProbability]

theorem bellmanStopProbability_terminal (r w : ℕ → ℕ → ℝ) (κ : ℝ) {N : ℕ}
    (hN : 0 < N) (k : ℕ) : bellmanStopProbability r w κ N N k = 1 := by
  simp [bellmanStopProbability,hN.ne']

def bellmanFlow (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N : ℕ) : Flow N :=
  policyFlow N (bellmanStopProbability r w κ N)

theorem bellmanFlow_cone (r w : ℕ → ℕ → ℝ) (κ : ℝ) {N : ℕ} (hN : 0 < N) :
    FlowCone (bellmanFlow r w κ N) := by
  apply policyFlow_cone
  · intro n k
    rcases bellmanStopProbability_binary r w κ N n k with h | h <;> rw [h] <;> norm_num
  · exact bellmanStopProbability_root r w κ N
  · intro k _
    exact bellmanStopProbability_terminal r w κ hN k

theorem bellmanFlow_intensity (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N : ℕ) :
    intensity (bellmanFlow r w κ N) = 1 :=
  policyFlow_intensity _ _ (bellmanStopProbability_root r w κ N)

theorem forcedBellman_recursion (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N n k : ℕ)
    (hn : 0 < n) (hnN : n < N) :
    forcedBellman r w κ N n k = max (r n k)
      (forcedBellman r w κ N (n+1) k+forcedBellman r w κ N (n+1) (k+1)-κ*w n k) := by
  simp only [forcedBellman,show n ≠ 0 by omega,show n+1 ≠ 0 by omega,ite_false]
  rw [show N-n = (N-(n+1))+1 by omega,bellman]

theorem bellmanStopProbability_complementarity (r w : ℕ → ℕ → ℝ) (κ : ℝ) (N n k : ℕ)
    (hn : n ≤ N) (hk : k ≤ n) (hroot : w 0 0 = 1) :
    bellmanStopProbability r w κ N n k*r n k+
      (1-bellmanStopProbability r w κ N n k)*
        (forcedBellman r w κ N (n+1) k+forcedBellman r w κ N (n+1) (k+1)-κ*w n k) =
      forcedBellman r w κ N n k := by
  by_cases hn0 : n = 0
  · have hk0 : k = 0 := by omega
    subst n
    subst k
    simp [bellmanStopProbability,forcedBellman,rootBellman,hroot]
  · by_cases hnN : n = N
    · subst n
      simp [bellmanStopProbability,forcedBellman,hn0,bellman]
    · have hlt : n < N := by omega
      rw [forcedBellman_recursion r w κ N n k (by omega) hlt]
      unfold bellmanStopProbability
      rw [ite_eq_right hn0,ite_eq_right (by omega : ¬N ≤ n)]
      split_ifs with h
      · rw [max_eq_left h]
        ring
      · rw [max_eq_right (le_of_not_ge h)]
        ring

theorem bellmanFlow_score (r w : ℕ → ℕ → ℝ) (κ : ℝ) {N : ℕ}
    (hN : 0 < N) (hroot : w 0 0 = 1) :
    rawFlowScore (bellmanFlow r w κ N) r w κ = rootBellman r w κ (N-1) := by
  have hf := bellmanFlow_cone r w κ hN
  have ht := raw_weighted_telescope (bellmanFlow r w κ N) hf (forcedBellman r w κ N)
  rw [bellmanFlow_intensity,one_mul,forcedBellman,ite_eq_left rfl] at ht
  rw [← ht]
  unfold rawFlowScore rawLayer rawChildren
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := by have h := Finset.mem_range.mp hn; omega
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
  simp only [bellmanFlow,raw_policyFlow_stop _ _ _ hnN,raw_policyFlow_continue _ _ _ hnN]
  have hc := bellmanStopProbability_complementarity r w κ N n k hnN hkn hroot
  nlinarith [congrArg (fun x : ℝ => policyArrival 1 (bellmanStopProbability r w κ N) n k*x) hc]

theorem flowScore_maximum (r w : ℕ → ℕ → ℝ) (κ : ℝ) {N : ℕ}
    (hN : 0 < N) (hroot : w 0 0 = 1) :
    (∀ f : Flow N, FlowCone f → intensity f = 1 → rawFlowScore f r w κ ≤ rootBellman r w κ (N-1)) ∧
    ∃ f : Flow N, FlowCone f ∧ intensity f = 1 ∧ rawFlowScore f r w κ = rootBellman r w κ (N-1) := by
  constructor
  · intro f hf hi
    simpa only [hi,one_mul] using flowScore_le_rootBellman f hf r w κ hroot
  · exact ⟨bellmanFlow r w κ N,bellmanFlow_cone r w κ hN,bellmanFlow_intensity r w κ N,
      bellmanFlow_score r w κ hN hroot⟩

end ThresholdHC.StoppingProgram
