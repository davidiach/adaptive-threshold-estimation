import ThresholdHC.OptimalQuantile.Root

/-! The partition series splits into the five-term partition sum and the tail
from the weight `32` on; for prices at least `64` that tail is at most `2^-62`. -/
noncomputable section
open Real
namespace ThresholdHC.QuantileFactorUpper
open ThresholdHC.OptimalQuantile

theorem partitionSeries_split {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u) :
    partitionSeries k u = finitePartition 5 k u+exponentialTail (32*dualPrice k u) := by
  have hs := exponentialTail_summable (dualPrice_ge_two hk hu)
  have h := hs.sum_add_tsum_nat_add 5
  have ht : ∀ i : ℕ, exp (1-dualPrice k u*(2 : ℝ)^(i+5)) =
      exp (1-32*dualPrice k u*(2 : ℝ)^i) := by
    intro i
    rw [pow_add]
    ring_nf
  simp only [ht] at h
  unfold partitionSeries finitePartition exponentialTail
  rw [← h, Fin.sum_univ_eq_sum_range (fun j => exp (1-dualPrice k u*(2 : ℝ)^j)) 5]
  ring

theorem exp_neg_nat_le (m : ℕ) : exp (-(m : ℝ)) ≤ (1/2 : ℝ)^m := by
  have h1 : exp (-1 : ℝ) ≤ 1/2 := by
    rw [exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have := add_one_le_exp (1 : ℝ)
    linarith
  have he : exp (-(m : ℝ)) = exp (-1)^m := by
    rw [← exp_nat_mul]
    ring_nf
  rw [he]
  exact pow_le_pow_left₀ (exp_pos _).le h1 m

theorem exponentialTail_le {p : ℝ} (hp : 64 ≤ p) : exponentialTail p ≤ 1/2^62 := by
  have hg : Summable (fun n : ℕ => (1/2 : ℝ)^63*(1/2 : ℝ)^n) :=
    (summable_geometric_two).mul_left _
  have hbound (n : ℕ) : exp (1-p*(2 : ℝ)^n) ≤ (1/2 : ℝ)^63*(1/2 : ℝ)^n := by
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ (2 : ℝ)^n by positivity)
    have h2 := power_two_lower n
    have hle : 1-p*(2 : ℝ)^n ≤ -((63+n : ℕ) : ℝ) := by
      push_cast
      nlinarith only [hm,h2]
    calc
      _ ≤ exp (-((63+n : ℕ) : ℝ)) := exp_le_exp.mpr hle
      _ ≤ (1/2 : ℝ)^(63+n) := exp_neg_nat_le _
      _ = _ := by rw [pow_add]
  have h := Summable.tsum_le_tsum hbound (exponentialTail_summable (by linarith)) hg
  rw [tsum_mul_left, tsum_geometric_two] at h
  unfold exponentialTail
  calc
    _ ≤ _ := h
    _ = _ := by norm_num

theorem partitionSeries_le_truncation {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u) :
    partitionSeries k u ≤ finitePartition 5 k u+1/2^62 := by
  rw [partitionSeries_split hk hu]
  have hp := dualPrice_ge_two hk hu
  have ht := exponentialTail_le (show (64 : ℝ) ≤ 32*dualPrice k u by linarith)
  linarith

end ThresholdHC.QuantileFactorUpper
