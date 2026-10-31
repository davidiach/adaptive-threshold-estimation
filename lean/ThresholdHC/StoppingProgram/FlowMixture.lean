import ThresholdHC.StoppingProgram.PolicyMixture

/-! Exact finite decision-table representation of every cone flow.
All positive-weight tables continue at the root and stop at the cap. -/

noncomputable section
open scoped BigOperators
namespace ThresholdHC.StoppingProgram

def flowDecisionParameters {N : ℕ} (f : Flow N) (s : CountState N) : ℝ :=
  countStopProbability f s.1.val s.2.val

theorem flowDecisionParameters_before {N : ℕ} (f : Flow N) (n k : ℕ) (hn : n < N) :
    arrayAt (flowDecisionParameters f) n k = countStopProbability f n k := by
  by_cases hk : k ≤ n
  · let s : CountState N := ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩
    exact arrayAt_state _ s
  · simp [arrayAt,show n ≤ N by omega,hk,countStopProbability,show n ≠ N by omega]

theorem flow_mixture_arrival {N : ℕ} (f : Flow N) (hf : FlowCone f) (n k : ℕ) (hn : n ≤ N) :
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      policyArrival (intensity f) (countDecision b) n k) =
      rawArray f.stopWeight n k+rawArray f.continueWeight n k := by
  rw [mixture_policyArrival _ _ n k hn]
  rw [policyArrival_congr_before (intensity f) (arrayAt (flowDecisionParameters f))
    (countStopProbability f) n k (fun j hj l => flowDecisionParameters_before f j l (by omega))]
  exact policyArrival_eq_raw f hf n k hn

theorem flow_mixture_weights {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*countDecision b s.1.val s.2.val)) =
        rawArray f.stopWeight s.1.val s.2.val ∧
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*(1-countDecision b s.1.val s.2.val))) =
        rawArray f.continueWeight s.1.val s.2.val := by
  have hs : s.1.val ≤ N := by have h := s.1.isLt; omega
  rw [mixture_arrival_stop,mixture_arrival_continue,flow_mixture_arrival f hf _ _ hs]
  exact ⟨by simpa only [flowDecisionParameters,mul_comm] using raw_stop_fraction f hf s.1.val s.2.val hs,
    by simpa only [flowDecisionParameters,mul_comm] using raw_continue_fraction f hf s.1.val s.2.val hs⟩

theorem positive_decision_zero {I : Type*} [Fintype I] (p : I → ℝ) (b : I → Bool) (i : I)
    (hp : p i = 0) (hb : 0 < decisionWeight p b) : b i = false := by
  cases hi : b i with
  | false => rfl
  | true =>
    have hz : decisionWeight p b = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [decisionFactor,hp,hi])
    linarith

theorem positive_decision_one {I : Type*} [Fintype I] (p : I → ℝ) (b : I → Bool) (i : I)
    (hp : p i = 1) (hb : 0 < decisionWeight p b) : b i = true := by
  cases hi : b i with
  | false =>
    have hz : decisionWeight p b = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [decisionFactor,hp,hi])
    linarith
  | true => rfl

theorem flow_mixture_supported_tables {N : ℕ} (f : Flow N) (hf : FlowCone f) (hN : 0 < N)
    (b : CountState N → Bool) (hb : 0 < decisionWeight (flowDecisionParameters f) b) :
    b (rootState N) = false ∧ ∀ s : CountState N, s.1.val = N → b s = true := by
  constructor
  · exact positive_decision_zero _ b _ (countStopProbability_root f hf hN) hb
  · intro s hs
    apply positive_decision_one _ b s _ hb
    simp only [flowDecisionParameters,countStopProbability,hs,ite_true]

theorem flow_mixture_probability {N : ℕ} (f : Flow N) (hf : FlowCone f) :
    (∀ b, 0 ≤ decisionWeight (flowDecisionParameters f) b) ∧
      (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b) = 1 :=
  ⟨decisionWeight_nonneg _ (fun s => countStopProbability_bounds f hf s.1.val s.2.val),decisionWeight_sum _⟩

end ThresholdHC.StoppingProgram
