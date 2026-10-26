import ThresholdHC.Proofs.Tier2.ClassifierBridge

noncomputable section

namespace ThresholdHC.Tier2

open ThresholdHC Uniform713

theorem finiteBoundary_mono_cap (k1 k2 : ℝ) (hk2 : 0 ≤ k2) (j : ℕ) {L K : ℕ}
    (hLK : L ≤ K) : finiteBoundary k1 k2 j L ≤ finiteBoundary k1 k2 j K := by
  unfold finiteBoundary thrK
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hk2
  exact Real.log_le_log (by positivity)
    (div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hLK)
      (by positivity))

theorem classifyK_work_mono (k1 k2 : ℝ) (hk2 : 0 ≤ k2) {L K M : ℕ}
    (hLK : L ≤ K) (x : Fin M → Bool) :
    ((classifyK k1 k2 L x).2 : ℝ) ≤ ((classifyK k1 k2 K x).2 : ℝ) := by
  rw [classifyK_work_eq_cap, classifyK_work_eq_cap]
  exact cap_mono (firstStop_mono _ _ hLK
    (fun j _ => finiteBoundary_mono_cap k1 k2 hk2 j hLK))

theorem levelWork_eq_classifyK_work (k1 k2 : ℝ) (hk2 : 0 ≤ k2) (l : ℕ)
    {M : ℕ} (x : Fin M → Bool) :
    levelWork k1 k2 l x = ((classifyK k1 k2 l x).2 : ℝ) := by
  by_cases hl : l = 0
  · simp only [levelWork, hl, ↓reduceIte]
  · simp only [levelWork, hl, ↓reduceIte]
    exact max_eq_left (classifyK_work_mono k1 k2 hk2 (Nat.sub_le l 1) x)

end ThresholdHC.Tier2
