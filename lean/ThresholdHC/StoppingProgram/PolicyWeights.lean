import ThresholdHC.StoppingProgram.FlowConservation

/-! Every cone flow has the count weights of a bounded randomized stopping
policy. At a count state its stopping probability is a/(a+c), with forced
stopping at the cap. No statistical realization is assumed here. -/

noncomputable section
namespace ThresholdHC.StoppingProgram

def policyArrival (rate : ℝ) (p : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,k => if k = 0 then rate else 0
  | n+1,k => policyArrival rate p n k*(1-p n k)+
      if 0 < k then policyArrival rate p n (k-1)*(1-p n (k-1)) else 0

theorem policyArrival_outside (rate : ℝ) (p : ℕ → ℕ → ℝ) (n k : ℕ) (hk : n < k) :
    policyArrival rate p n k = 0 := by
  induction n generalizing k with
  | zero => simp [policyArrival,show k ≠ 0 by omega]
  | succ n ih =>
    simp only [policyArrival,ih k (by omega),zero_mul,zero_add,
      show 0 < k by omega,ite_true,ih (k-1) (by omega)]

theorem arrayAt_nonneg {N : ℕ} (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) (n k : ℕ) :
    0 ≤ arrayAt u n k := by
  unfold arrayAt
  split_ifs <;> first | exact hu _ | exact le_rfl

def countStopProbability {N : ℕ} (f : Flow N) (n k : ℕ) : ℝ :=
  if n = N then 1 else arrayAt f.stopWeight n k/(arrayAt f.stopWeight n k+arrayAt f.continueWeight n k)

theorem countStopProbability_bounds {N : ℕ} (f : Flow N) (hf : FlowCone f) (n k : ℕ) :
    0 ≤ countStopProbability f n k ∧ countStopProbability f n k ≤ 1 := by
  unfold countStopProbability
  split_ifs
  · norm_num
  · have ha := arrayAt_nonneg _ hf.stop_nonneg n k
    have hc := arrayAt_nonneg _ hf.continue_nonneg n k
    exact ⟨div_nonneg ha (add_nonneg ha hc),div_le_one_of_le₀ (by linarith) (by positivity)⟩

theorem countStopProbability_root {N : ℕ} (f : Flow N) (hf : FlowCone f) (hN : 0 < N) :
    countStopProbability f 0 0 = 0 := by
  rw [countStopProbability,ite_eq_right (by omega)]
  change f.stopWeight (rootState N)/(f.stopWeight (rootState N)+f.continueWeight (rootState N)) = 0
  rw [hf.root_stop,zero_div]

theorem raw_stop_fraction {N : ℕ} (f : Flow N) (hf : FlowCone f) (n k : ℕ) (_hn : n ≤ N) :
    (rawArray f.stopWeight n k+rawArray f.continueWeight n k)*countStopProbability f n k =
      rawArray f.stopWeight n k := by
  by_cases he : n = N
  · rw [countStopProbability,ite_eq_left he,he,rawArray_terminal f hf,add_zero,mul_one]
  · have ha := arrayAt_nonneg _ hf.stop_nonneg n k
    have hc := arrayAt_nonneg _ hf.continue_nonneg n k
    rw [countStopProbability,ite_eq_right he]
    unfold rawArray
    by_cases hz : arrayAt f.stopWeight n k+arrayAt f.continueWeight n k = 0
    · have ha0 : arrayAt f.stopWeight n k = 0 := by linarith
      simp [ha0]
    · field_simp

theorem raw_continue_fraction {N : ℕ} (f : Flow N) (hf : FlowCone f) (n k : ℕ) (hn : n ≤ N) :
    (rawArray f.stopWeight n k+rawArray f.continueWeight n k)*(1-countStopProbability f n k) =
      rawArray f.continueWeight n k := by
  have h := raw_stop_fraction f hf n k hn
  nlinarith

theorem policyArrival_eq_raw {N : ℕ} (f : Flow N) (hf : FlowCone f) (n k : ℕ) (hn : n ≤ N) :
    policyArrival (intensity f) (countStopProbability f) n k =
      rawArray f.stopWeight n k+rawArray f.continueWeight n k := by
  by_cases hk : k ≤ n
  · induction n generalizing k with
    | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp only [policyArrival,ite_true,rawArray,Nat.choose_zero_right,Nat.cast_one,one_mul]
      change intensity f = f.stopWeight (rootState N)+intensity f
      rw [hf.root_stop,zero_add]
    | succ n ih =>
      rw [policyArrival,raw_flow_recursion f hf (n+1) k (by omega) hn hk]
      simp only [Nat.add_sub_cancel]
      have hprev (j : ℕ) : policyArrival (intensity f) (countStopProbability f) n j =
          rawArray f.stopWeight n j+rawArray f.continueWeight n j := by
        by_cases hj : j ≤ n
        · exact ih j (by omega) hj
        · simp only [policyArrival_outside _ _ n j (by omega),rawArray_outside _ n j (by omega),add_zero]
      rw [hprev k,raw_continue_fraction f hf n k (by omega)]
      split_ifs with hkpos
      · rw [hprev (k-1),raw_continue_fraction f hf n (k-1) (by omega)]
      · rfl
  · simp only [policyArrival_outside _ _ n k (by omega),rawArray_outside _ n k (by omega),add_zero]

theorem policy_weights_realize_flow {N : ℕ} (f : Flow N) (hf : FlowCone f) :
    ∀ n k, n ≤ N →
      policyArrival (intensity f) (countStopProbability f) n k*countStopProbability f n k = rawArray f.stopWeight n k ∧
      policyArrival (intensity f) (countStopProbability f) n k*(1-countStopProbability f n k) = rawArray f.continueWeight n k := by
  intro n k hn
  rw [policyArrival_eq_raw f hf n k hn]
  exact ⟨raw_stop_fraction f hf n k hn,raw_continue_fraction f hf n k hn⟩

end ThresholdHC.StoppingProgram
