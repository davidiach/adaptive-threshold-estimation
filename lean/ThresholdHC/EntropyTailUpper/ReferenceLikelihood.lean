import ThresholdHC.EntropyTailUpper.ScoreHitting
import ThresholdHC.EntropyTailUpper.BankErrors

/-! Exact conversion between the logarithmic score used for work and the
prefix likelihoods used for error control. -/

noncomputable section
open MeasureTheory Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.CriticalEntropy

theorem negative_score_likelihood {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1/2)
    {n : ℕ} (w : Fin n → Bool) :
    streamProb (1/2-r) w = streamProb (1/2) w * exp (∑ i, negativeBitScore r (w i)) := by
  simp only [streamProb, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases w i <;> simp only [Bool.false_eq_true, ite_false, ite_true, negativeBitScore]
  · rw [exp_log (by linarith : 0 < 1+2*r)]
    ring
  · rw [exp_log (by linarith : 0 < 1-2*r)]
    ring

theorem negative_score_crossing {r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1/2) (hc : 0 < c)
    {n : ℕ} (w : Fin n → Bool) (hh : log c⁻¹ ≤ ∑ i, negativeBitScore r (w i)) :
    streamProb (1/2) w ≤ c * streamProb (1/2-r) w := by
  rw [negative_score_likelihood hr0 hr1]
  have h := exp_le_exp.mpr hh
  rw [exp_log (inv_pos.mpr hc)] at h
  have hm := mul_le_mul_of_nonneg_left h hc.le
  rw [mul_inv_cancel₀ hc.ne'] at hm
  have hf := streamProb_pos (1/2) (by norm_num) (by norm_num) w
  nlinarith only [mul_le_mul_of_nonneg_left hm hf.le]

def positiveBitScore (r : ℝ) (x : Bool) : ℝ := negativeBitScore r (!x)

theorem positive_score_likelihood {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1/2)
    {n : ℕ} (w : Fin n → Bool) :
    streamProb (1/2+r) w = streamProb (1/2) w * exp (∑ i, positiveBitScore r (w i)) := by
  simp only [streamProb, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases w i <;> simp only [Bool.false_eq_true, ite_false, ite_true, positiveBitScore,
    Bool.not_false, Bool.not_true, negativeBitScore]
  · rw [exp_log (by linarith : 0 < 1-2*r)]
    ring
  · rw [exp_log (by linarith : 0 < 1+2*r)]
    ring

theorem positiveBitScore_affine {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1/2) (x : Bool) :
    positiveBitScore r x = (1/2)*log (1-4*r^2)+(bit x-1/2)*log ((1+2*r)/(1-2*r)) := by
  have hm : 0 < 1-2*r := by linarith
  have hp : 0 < 1+2*r := by linarith
  rw [show 1-4*r^2 = (1-2*r)*(1+2*r) by ring, log_mul hm.ne' hp.ne', log_div hp.ne' hm.ne']
  cases x <;> simp only [positiveBitScore, negativeBitScore, bit, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true] <;> ring

theorem positive_prefix_score {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1/2)
    {n : ℕ} (hn : 0 < n) (ω : ℕ → Bool) :
    (∑ i : Fin n, positiveBitScore r (tapePrefix n ω i)) =
      n*((1/2)*log (1-4*r^2)+(ThresholdHC.Uniform713.prefixMean observations n ω-1/2)*
        log ((1+2*r)/(1-2*r))) := by
  simp_rw [positiveBitScore_affine hr0 hr1]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, tapePrefix]
  rw [Fin.sum_univ_eq_sum_range (fun i => bit (ω i))]
  unfold ThresholdHC.Uniform713.prefixMean observations
  have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem positive_prefix_score_lower {d r : ℝ} (hd : 0 ≤ d)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (hdr : d/4 ≤ r) (hrd : r ≤ d/2)
    {n : ℕ} (hn : 0 < n) (ω : ℕ → Bool)
    (hm : d/2 ≤ ThresholdHC.Uniform713.prefixMean observations n ω-1/2) :
    n*d^2/3 ≤ ∑ i : Fin n, positiveBitScore r (tapePrefix n ω i) := by
  rw [positive_prefix_score hr0 (by linarith) hn]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (positiveReferenceDrift_lower hd hr0 hr1 hdr hrd hm) (Nat.cast_nonneg n : (0:ℝ) ≤ n)

end ThresholdHC.EntropyTailUpper
