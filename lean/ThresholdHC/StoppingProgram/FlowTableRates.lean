import ThresholdHC.StoppingProgram.TableStatistics

/-! Poisson activation rates for the finite deterministic table mixture. -/

noncomputable section
open scoped BigOperators
namespace ThresholdHC.StoppingProgram

theorem policyArrival_mul (rate : ℝ) (p : ℕ → ℕ → ℝ) (n k : ℕ) :
    policyArrival rate p n k = rate*policyArrival 1 p n k := by
  induction n generalizing k with
  | zero => simp only [policyArrival]; split_ifs <;> ring
  | succ n ih =>
    simp only [policyArrival,ih]
    split_ifs <;> ring

def flowTableRate {N : ℕ} (f : Flow N) (b : CountState N → Bool) : ℝ :=
  intensity f*decisionWeight (flowDecisionParameters f) b

theorem flowTableRate_nonneg {N : ℕ} (f : Flow N) (hf : FlowCone f) (b : CountState N → Bool) :
    0 ≤ flowTableRate f b := mul_nonneg (hf.continue_nonneg (rootState N)) ((flow_mixture_probability f hf).1 b)

theorem flowTableRate_sum {N : ℕ} (f : Flow N) : ∑ b : CountState N → Bool, flowTableRate f b = intensity f := by
  simp only [flowTableRate,← Finset.mul_sum,decisionWeight_sum,mul_one]

theorem flowTableRate_supported {N : ℕ} (f : Flow N) (hf : FlowCone f) (hN : 0 < N)
    (b : CountState N → Bool) (hr : flowTableRate f b ≠ 0) :
    b (rootState N) = false ∧ ∀ s : CountState N, s.1.val = N → b s = true := by
  apply flow_mixture_supported_tables f hf hN b
  have hn : decisionWeight (flowDecisionParameters f) b ≠ 0 := by
    intro h
    apply hr
    simp [flowTableRate,h]
  exact lt_of_le_of_ne ((flow_mixture_probability f hf).1 b) (Ne.symm hn)

theorem flowTableRate_stop {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    (∑ b : CountState N → Bool, flowTableRate f b*
      (policyArrival 1 (countDecision b) s.1.val s.2.val*countDecision b s.1.val s.2.val)) =
        rawArray f.stopWeight s.1.val s.2.val := by
  rw [← (flow_mixture_weights f hf s).1]
  apply Finset.sum_congr rfl
  intro b _
  rw [policyArrival_mul (intensity f)]
  unfold flowTableRate
  ring

theorem flowTableRate_continue {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    (∑ b : CountState N → Bool, flowTableRate f b*
      (policyArrival 1 (countDecision b) s.1.val s.2.val*(1-countDecision b s.1.val s.2.val))) =
        rawArray f.continueWeight s.1.val s.2.val := by
  rw [← (flow_mixture_weights f hf s).2]
  apply Finset.sum_congr rfl
  intro b _
  rw [policyArrival_mul (intensity f)]
  unfold flowTableRate
  ring

theorem rawArray_mul {N : ℕ} (a y : CountState N → ℝ) (n k : ℕ) :
    rawArray (fun s => a s*y s) n k = rawArray a n k*arrayAt y n k := by
  unfold rawArray arrayAt
  split_ifs <;> ring

end ThresholdHC.StoppingProgram
