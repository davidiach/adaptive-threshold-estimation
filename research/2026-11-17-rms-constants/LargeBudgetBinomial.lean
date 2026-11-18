import LargeBudgetFresh

noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget

private def term (p : ℝ) (f : ℕ → ℝ) (n j k : ℕ) :=
  (n.choose j : ℝ)*p^j*(1-p)^(n-j)*f (k+j)

theorem binomial_sum (p : ℝ) (f : ℕ → ℝ) (n k : ℕ) :
    binomialAverage p f n k = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*p^j*(1-p)^(n-j)*f (k+j) := by
  change _ = ∑ j ∈ Finset.range (n+1), term p f n j k
  induction n generalizing k with
  | zero => simp [binomialAverage,term]
  | succ n ih =>
    rw [binomialAverage,ih,ih,Finset.mul_sum,Finset.mul_sum]
    have left : (1-p)*term p f n 0 k = term p f (n+1) 0 k := by simp [term,pow_succ]; ring
    have right : p*term p f n n (k+1) = term p f (n+1) (n+1) k := by
      simp [term,pow_succ,show k+1+n=k+(n+1) by omega]; ring
    have mid (j : ℕ) (hj : j<n) : (1-p)*term p f n (j+1) k + p*term p f n j (k+1) =
        term p f (n+1) (j+1) k := by
      unfold term
      rw [Nat.choose_succ_succ,Nat.cast_add,show k+1+j=k+(j+1) by omega,
        show n+1-(j+1)=n-j by omega,show n-j=n-(j+1)+1 by omega]
      simp only [pow_succ]
      ring
    have sums := Finset.sum_congr (s₁:=Finset.range n) rfl (fun j hj => mid j (Finset.mem_range.mp hj))
    rw [Finset.sum_add_distrib] at sums
    rw [Finset.sum_range_succ' (fun j => (1-p)*term p f n j k),
      Finset.sum_range_succ (fun j => p*term p f n j (k+1)),left,right,
      Finset.sum_range_succ (fun j => term p f (n+1) j k),
      Finset.sum_range_succ' (fun j => term p f (n+1) j k)]
    linarith only [sums]

end ThresholdHC.SharpRMS.LargeBudget
