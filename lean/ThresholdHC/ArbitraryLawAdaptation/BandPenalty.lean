import ThresholdHC.ArbitraryLawAdaptation.EntropyTransport

/-! The geometric code for upward band transport. A displacement by `k`
bands contracts inverse-square cost by at most `min 1 (4 / 4^k)`.
The estimates here are uniform in both finite index-set sizes. -/

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.EntropyTailQuantile

def bandContraction (k : ℕ) : ℝ := min 1 (4 * (1/4:ℝ)^k)

theorem bandContraction_nonneg (k : ℕ) : 0 ≤ bandContraction k := by
  unfold bandContraction
  positivity

theorem bandContraction_le_one (k : ℕ) : bandContraction k ≤ 1 := min_le_left _ _

theorem quarter_power_linear (k : ℕ) : (1/4:ℝ)^k*((k:ℝ)+2) ≤ 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    push_cast
    have h := mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) k)
      (show 0 ≤ 3*(k:ℝ)+5 by positivity)
    nlinarith

theorem bandContraction_weighted (k : ℕ) : bandContraction k*((k:ℝ)+1) ≤ 2 := by
  cases k with
  | zero => norm_num [bandContraction]
  | succ k =>
    have h := mul_le_mul_of_nonneg_right
      (min_le_right 1 (4*(1/4:ℝ)^(k+1))) (show 0 ≤ ((k+1:ℕ):ℝ)+1 by positivity)
    have he : 4*(1/4:ℝ)^(k+1)*(((k+1:ℕ):ℝ)+1) = (1/4:ℝ)^k*((k:ℝ)+2) := by
      rw [pow_succ]
      push_cast
      ring
    exact h.trans (he.le.trans (quarter_power_linear k))

theorem half_power_sum (n : ℕ) :
    (∑ k : Fin n, (1/2:ℝ)^(k.val+1)) = 1-(1/2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih,pow_succ]
    ring

theorem bandContraction_code (k : ℕ) :
    bandContraction k * (-log ((1/2:ℝ)^(k+1))) ≤ 2 := by
  have hlog : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hnonneg : 0 ≤ log 2 := log_nonneg (by norm_num)
  have he : -log ((1/2:ℝ)^(k+1)) = ((k:ℝ)+1)*log 2 := by
    simp [log_pow]
  rw [he,← mul_assoc]
  exact (mul_le_mul_of_nonneg_right (bandContraction_weighted k) hnonneg).trans
    (by linarith)

theorem finite_band_transport_three {ι : Type*} [Fintype ι] {n : ℕ}
    {a : ι → ℝ} {f b : ι × Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i, (∑ k, f (i,k)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2.val * f x) :
    costEntropy b ≤ 3*costEntropy a := by
  have h := costEntropy_contracting_transport ha hf hb hrow hcost
    (fun k => bandContraction_le_one k.val)
    (fun k => by positivity : ∀ k : Fin n, 0 < (1/2:ℝ)^(k.val+1))
    (by rw [half_power_sum]; exact sub_le_self _ (pow_nonneg (by norm_num) n))
    (by norm_num : (0:ℝ) ≤ 2) (fun k => bandContraction_code k.val)
  have hbase := costTotal_le_costEntropy ha
  linarith

end ThresholdHC.ArbitraryLawAdaptation
