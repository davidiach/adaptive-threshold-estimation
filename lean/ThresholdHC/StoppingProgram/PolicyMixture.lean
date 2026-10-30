import ThresholdHC.StoppingProgram.PolicyWeights
import ThresholdHC.StoppingProgram.DecisionIndependence

/-! Finite deterministic decision tables reproduce the exact randomized
arrival and stopping weights. Decisions at a depth are independent of arrival. -/

noncomputable section
open scoped BigOperators
namespace ThresholdHC.StoppingProgram

def countDecision {N : ℕ} (b : CountState N → Bool) (n k : ℕ) : ℝ :=
  arrayAt (fun s => if b s then 1 else 0) n k

theorem countDecision_state {N : ℕ} (b : CountState N → Bool) (s : CountState N) :
    countDecision b s.1.val s.2.val = if b s then 1 else 0 := arrayAt_state _ s

theorem policyArrival_congr_before (rate : ℝ) (p r : ℕ → ℕ → ℝ) (n k : ℕ)
    (h : ∀ j, j < n → ∀ l, p j l = r j l) : policyArrival rate p n k = policyArrival rate r n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [policyArrival,ih k (fun j hj => h j (by omega)),h n (by omega),
      ih (k-1) (fun j hj => h j (by omega))]

theorem arrival_independent_current {N : ℕ} (rate : ℝ) (s : CountState N) :
    ∀ b t, policyArrival rate (countDecision (Function.update b s t)) s.1.val s.2.val =
      policyArrival rate (countDecision b) s.1.val s.2.val := by
  intro b t
  apply policyArrival_congr_before
  intro n hn k
  unfold countDecision arrayAt
  split_ifs with hN hk
  · have hne : (⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩ : CountState N) ≠ s := by
      intro he
      have hval := congrArg (fun z : CountState N => z.1.val) he
      dsimp only at hval
      omega
    simp only [Function.update_of_ne hne]
  · rfl
  · rfl

theorem mixture_arrival_continue {N : ℕ} (rate : ℝ) (p : CountState N → ℝ) (s : CountState N) :
    (∑ b : CountState N → Bool, decisionWeight p b*
      (policyArrival rate (countDecision b) s.1.val s.2.val*(1-countDecision b s.1.val s.2.val))) =
      (1-p s)*(∑ b : CountState N → Bool, decisionWeight p b*policyArrival rate (countDecision b) s.1.val s.2.val) := by
  simp only [countDecision_state]
  have h := independent_decision_factor p s
    (fun b => policyArrival rate (countDecision b) s.1.val s.2.val)
    (arrival_independent_current rate s) (fun b => 1-(if b then 1 else 0))
  simpa only [Bool.false_eq_true,ite_false,ite_true,sub_zero,sub_self,mul_one,mul_zero,add_zero] using h

theorem mixture_arrival_stop {N : ℕ} (rate : ℝ) (p : CountState N → ℝ) (s : CountState N) :
    (∑ b : CountState N → Bool, decisionWeight p b*
      (policyArrival rate (countDecision b) s.1.val s.2.val*countDecision b s.1.val s.2.val)) =
      p s*(∑ b : CountState N → Bool, decisionWeight p b*policyArrival rate (countDecision b) s.1.val s.2.val) := by
  simp only [countDecision_state]
  have h := independent_decision_factor p s
    (fun b => policyArrival rate (countDecision b) s.1.val s.2.val)
    (arrival_independent_current rate s) (fun b => if b then 1 else 0)
  simpa only [Bool.false_eq_true,ite_false,ite_true,mul_one,mul_zero,zero_add] using h

theorem mixture_policyArrival {N : ℕ} (rate : ℝ) (p : CountState N → ℝ) (n k : ℕ) (hn : n ≤ N) :
    (∑ b : CountState N → Bool, decisionWeight p b*policyArrival rate (countDecision b) n k) =
      policyArrival rate (arrayAt p) n k := by
  induction n generalizing k with
  | zero =>
    simp only [policyArrival]
    rw [← Finset.sum_mul,decisionWeight_sum,one_mul]
  | succ n ih =>
    have hpart (j : ℕ) : (∑ b : CountState N → Bool, decisionWeight p b*
        (policyArrival rate (countDecision b) n j*(1-countDecision b n j))) =
        policyArrival rate (arrayAt p) n j*(1-arrayAt p n j) := by
      by_cases hj : j ≤ n
      · let s : CountState N := ⟨⟨n,by omega⟩,⟨j,by change j < n+1; omega⟩⟩
        have hh := mixture_arrival_continue rate p s
        change (∑ b : CountState N → Bool, decisionWeight p b*
          (policyArrival rate (countDecision b) n j*(1-countDecision b n j))) =
          (1-p s)*(∑ b : CountState N → Bool, decisionWeight p b*policyArrival rate (countDecision b) n j) at hh
        rw [ih j (by omega)] at hh
        rw [hh,show arrayAt p n j = p s from arrayAt_state p s]
        ring
      · simp only [policyArrival_outside _ _ n j (by omega),zero_mul,mul_zero,Finset.sum_const_zero]
    simp only [policyArrival,mul_add,Finset.sum_add_distrib]
    rw [hpart k]
    split_ifs with hk
    · rw [hpart (k-1)]
    · simp

end ThresholdHC.StoppingProgram
