import ThresholdHC.EntropyTailUpper.ReferenceLikelihood

/-! A pointwise Gaussian envelope for every all-negative prefix, including
the deterministic endpoint gap one half. -/

noncomputable section
open Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.CriticalEntropy

theorem negativeBitScore_affine {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1/2) (x : Bool) :
    negativeBitScore r x = (1/2)*log (1-4*r^2)-(bit x-1/2)*log ((1+2*r)/(1-2*r)) := by
  have hm : 0 < 1-2*r := by linarith
  have hp : 0 < 1+2*r := by linarith
  rw [show 1-4*r^2 = (1-2*r)*(1+2*r) by ring, log_mul hm.ne' hp.ne', log_div hp.ne' hm.ne']
  cases x <;> simp only [negativeBitScore, bit, Bool.false_eq_true, ite_false, ite_true] <;> ring

theorem negative_prefix_score {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1/2)
    {n : ℕ} (w : Fin n → Bool) :
    (∑ i, negativeBitScore r (w i)) =
      n*(1/2)*log (1-4*r^2)-((∑ i, bit (w i))-n/2)*log ((1+2*r)/(1-2*r)) := by
  simp_rw [negativeBitScore_affine hr0 hr1]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem negative_prefix_gaussian_interior {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1/2)
    {n : ℕ} (w : Fin n → Bool) (hw : (n:ℝ)/2 ≤ ∑ i, bit (w i)) :
    streamProb (1/2-d) w ≤ streamProb (1/2) w * exp (-2*n*d^2) := by
  rw [negative_score_likelihood hd0 hd1]
  have hz : 0 < 1-4*d^2 := by nlinarith
  have hl := log_le_sub_one_of_pos hz
  have hr : 0 ≤ log ((1+2*d)/(1-2*d)) :=
    log_nonneg ((one_le_div (by linarith : 0 < 1-2*d)).mpr (by linarith))
  have hmul := mul_nonneg (sub_nonneg.mpr hw) hr
  have hbase := mul_le_mul_of_nonneg_left hl (show 0 ≤ (n:ℝ)*(1/2) by positivity)
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (streamProb_pos (1/2) (by norm_num) (by norm_num) w).le
  rw [negative_prefix_score hd0 hd1]
  nlinarith only [hmul, hbase]

theorem negative_prefix_gaussian {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1/2)
    {n : ℕ} (w : Fin n → Bool) (hw : (n:ℝ)/2 ≤ ∑ i, bit (w i)) :
    streamProb (1/2-d) w ≤ streamProb (1/2) w * exp (-2*n*d^2) := by
  by_cases hd : d < 1/2
  · exact negative_prefix_gaussian_interior hd0 hd w hw
  have hd : d = 1/2 := le_antisymm hd1 (le_of_not_gt hd)
  subst d
  by_cases hn : n = 0
  · subst n; simp [streamProb]
  have hex : ∃ i, w i = true := by
    by_contra h
    have hf : ∀ i, w i = false := by
      intro i
      cases hi : w i
      · rfl
      · exact False.elim (h ⟨i, hi⟩)
    simp only [hf, bit, Bool.false_eq_true, ite_false, Finset.sum_const_zero] at hw
    have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    linarith
  obtain ⟨i, hi⟩ := hex
  have hz : streamProb (1/2-1/2) w = 0 := by
    unfold streamProb
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
  rw [hz]
  exact mul_nonneg (streamProb_pos (1/2) (by norm_num) (by norm_num) w).le (exp_pos _).le

end ThresholdHC.EntropyTailUpper
