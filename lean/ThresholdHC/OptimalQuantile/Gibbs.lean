import ThresholdHC.EntropyTailQuantile.CostEntropy

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.OptimalQuantile
open ThresholdHC.EntropyTailQuantile

theorem exponential_entropy {I : Type} [Fintype I] (w : I → ℝ) (price : ℝ) :
    costEntropy (fun i => exp (1-price*w i)) =
      price*(∑ i, w i*exp (1-price*w i))+
        costTotal (fun i => exp (1-price*w i))*log (costTotal (fun i => exp (1-price*w i))) := by
  have he : (∑ i, -exp (1-price*w i)*(1-price*w i)) =
      -costTotal (fun i => exp (1-price*w i))+price*(∑ i, w i*exp (1-price*w i)) := by
    calc
      _ = ∑ i, (-exp (1-price*w i)+price*(w i*exp (1-price*w i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_neg_distrib,← Finset.mul_sum]
        rfl
  simp only [costEntropy,negMulLog,log_exp]
  rw [he]
  ring

/-- A finite weighted entropy inequality is equivalent to its exponential
partition sum being at most one. Empty index types are included. -/
theorem weighted_entropy_iff_partition {I : Type} [Fintype I] (w : I → ℝ) (price : ℝ) :
    (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → costEntropy x ≤ price*(∑ i, w i*x i)) ↔
      (∑ i, exp (1-price*w i)) ≤ 1 := by
  constructor
  · intro h
    let Z := costTotal (fun i => exp (1-price*w i))
    have hZ : 0 ≤ Z := costTotal_nonneg (fun i => (exp_pos _).le)
    rcases hZ.eq_or_lt with hz | hz
    · change Z ≤ 1
      rw [← hz]
      norm_num
    have he := h (fun i => exp (1-price*w i)) (fun i => (exp_pos _).le)
    rw [exponential_entropy] at he
    have hl : log Z ≤ 0 := by
      have hp : Z*log Z ≤ 0 := by dsimp [Z]; linarith
      exact nonpos_of_mul_nonpos_right hp hz
    have hbound := (log_le_iff_le_exp hz).mp hl
    simpa only [exp_zero,Z,costTotal] using hbound
  · intro h x hx
    have he := costEntropy_le_reference hx (fun i => exp_pos (1-price*w i)) h
    simp only [log_exp,sub_sub_cancel] at he
    calc
      _ ≤ ∑ i, x i*(price*w i) := he
      _ = price*(∑ i, w i*x i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

end ThresholdHC.OptimalQuantile
