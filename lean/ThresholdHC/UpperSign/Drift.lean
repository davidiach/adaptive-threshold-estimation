import ThresholdHC.UpperSign.EarlyStop

/-! The drift bounds below the split, in closed form.

At the check `k` of the cap-`2^L` classifier, with `J = L - k`, the drift bound
is `exp(-2*(sqrt v_J - sqrt y)^2)` with `v_J = 1 + J*log 2` and
`y = cap k*d^2 ≤ cap L*d^2/2^J`; it increases with `y`. So the drift bounds of a
classifier with `cap L*d^2 ≤ Y` add up to at most the series
`∑_J driftTerm J Y` (`driftSum_le`). For `Y = (3/8)/2^m`, `m = 0, …, 4`, the
series is bounded by its first six terms, evaluated with rational bounds and a
Taylor lower bound for the exponential, plus a geometric tail
(`driftSeries_le_0` to `driftSeries_le_4`). -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

section Drift
open Real Uniform713

/-- The drift term at level difference `J` for the scale `Y`. -/
def driftTerm (J : ℕ) (Y : ℝ) : ℝ :=
  Real.exp (-2 * (Real.sqrt (1 + J * Real.log 2) - Real.sqrt (Y / 2 ^ J)) ^ 2)

theorem driftTerm_nonneg (J : ℕ) (Y : ℝ) : 0 ≤ driftTerm J Y := (Real.exp_pos _).le

/-- One numeric drift term: `a ≤ sqrt v`, `sqrt y ≤ b ≤ a`. -/
theorem drift_term_le {J : ℕ} {y a b c : ℝ} (hb0 : 0 ≤ b) (ha : a ^ 2 ≤ 1 + J * Real.log 2)
    (hy : y ≤ b ^ 2) (hba : b ≤ a)
    (htay : 1 ≤ c * ∑ i ∈ range 8, (2 * (a - b) ^ 2) ^ i / (i.factorial : ℝ)) :
    Real.exp (-2 * (Real.sqrt (1 + J * Real.log 2) - Real.sqrt y) ^ 2) ≤ c := by
  have hav : a ≤ Real.sqrt (1 + J * Real.log 2) := Real.le_sqrt_of_sq_le ha
  have hyb : Real.sqrt y ≤ b := (Real.sqrt_le_left hb0).2 hy
  have hd : (a - b) ^ 2 ≤ (Real.sqrt (1 + J * Real.log 2) - Real.sqrt y) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  refine (Real.exp_le_exp.2 (by linarith : -2 * (Real.sqrt (1 + J * Real.log 2) - Real.sqrt y) ^ 2 ≤
    -(2 * (a - b) ^ 2))).trans ?_
  exact UpperWork.exp_neg_le_of_taylor (by positivity) 8 htay

/-- Far drift terms decay geometrically. -/
theorem driftTerm_tail {J : ℕ} (hJ : 7 ≤ J) {Y : ℝ} (hY : Y ≤ 3 / 8) :
    driftTerm J Y ≤ (31 / 100) ^ J := by
  have hl := Real.log_two_gt_d9
  have hJr : (7 : ℝ) ≤ J := by exact_mod_cast hJ
  set v := 1 + (J : ℝ) * Real.log 2 with hv
  have hv1 : 1 ≤ v := by simp only [hv]; nlinarith
  have hsv : 1 ≤ Real.sqrt v := Real.one_le_sqrt.2 hv1
  have hpow : (128 : ℝ) ≤ 2 ^ J := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJ
    norm_num at this ⊢
    linarith
  have hy : Y / 2 ^ J ≤ (3 / 50) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsy : Real.sqrt (Y / 2 ^ J) ≤ 3 / 50 := (Real.sqrt_le_left (by norm_num)).2 hy
  have hgap : (47 / 50) * Real.sqrt v ≤ Real.sqrt v - Real.sqrt (Y / 2 ^ J) := by nlinarith
  have hsq : (47 / 50) ^ 2 * v ≤ (Real.sqrt v - Real.sqrt (Y / 2 ^ J)) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hgap 2
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h
    exact h
  have he : Real.exp (-(6 / 5 : ℝ)) ≤ 31 / 100 :=
    UpperWork.exp_neg_le_of_taylor (by norm_num) 8
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  unfold driftTerm
  calc
    _ ≤ Real.exp (-(6 / 5 : ℝ) * J) := by
      apply Real.exp_le_exp.2
      nlinarith
    _ = Real.exp (-(6 / 5 : ℝ)) ^ J := by rw [mul_comm, Real.exp_nat_mul]
    _ ≤ (31 / 100) ^ J := pow_le_pow_left₀ (Real.exp_pos _).le he J

/-- Keep the first six drift terms; the rest add at most `1/2000`. -/
theorem driftSeries_split (L : ℕ) (Y : ℝ) (hY : Y ≤ 3 / 8) :
    ∑ J ∈ range L, driftTerm (J + 1) Y ≤
      driftTerm 1 Y + driftTerm 2 Y + driftTerm 3 Y + driftTerm 4 Y + driftTerm 5 Y +
        driftTerm 6 Y + 1 / 2000 := by
  have hsplit : ∑ J ∈ range L, driftTerm (J + 1) Y ≤
      ∑ J ∈ range 6, driftTerm (J + 1) Y + ∑ J ∈ range L, driftTerm (6 + J + 1) Y := by
    rw [← Finset.sum_range_add]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun J _ _ => driftTerm_nonneg _ _)
  have htail : ∑ J ∈ range L, driftTerm (6 + J + 1) Y ≤ 1 / 2000 := by
    calc
      _ ≤ ∑ J ∈ range L, (31 / 100 : ℝ) ^ 7 * (31 / 100) ^ J := by
        apply sum_le_sum
        intro J _
        refine (driftTerm_tail (by omega) hY).trans (le_of_eq ?_)
        rw [← pow_add]
        ring_nf
      _ = (31 / 100 : ℝ) ^ 7 * ∑ J ∈ range L, (31 / 100 : ℝ) ^ J := by rw [mul_sum]
      _ ≤ (31 / 100 : ℝ) ^ 7 * (100 / 69) := by
        gcongr
        have hs := sum_le_hasSum (range L) (fun J _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 31 / 100) J)
          (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 31 / 100) (by norm_num))
        refine hs.trans (le_of_eq ?_)
        norm_num
      _ ≤ 1 / 2000 := by norm_num
  have h6 : ∑ J ∈ range 6, driftTerm (J + 1) Y = driftTerm 1 Y + driftTerm 2 Y + driftTerm 3 Y +
      driftTerm 4 Y + driftTerm 5 Y + driftTerm 6 Y := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [h6] at hsplit
  linarith

end Drift

section DriftNumeric
open Real Uniform713

theorem driftSeries_le_0 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (3 / 8 : ℝ) ≤ (56477 / 200000 : ℝ) := by
  refine (driftSeries_split L (3 / 8 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (3 / 16 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (433013 / 1000000 : ℝ)) (c := (27687 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (3 / 32 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (306187 / 1000000 : ℝ)) (c := (23571 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (3 / 64 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (216507 / 1000000 : ℝ)) (c := (154 / 15625 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (3 / 128 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (76547 / 500000 : ℝ)) (c := (2413 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (3 / 256 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (54127 / 500000 : ℝ)) (c := (721 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (3 / 512 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (76547 / 1000000 : ℝ)) (c := (257 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem driftSeries_le_1 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (3 / 16 : ℝ) ≤ (178521 / 1000000 : ℝ) := by
  refine (driftSeries_split L (3 / 16 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (3 / 32 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (306187 / 1000000 : ℝ)) (c := (138193 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (3 / 64 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (216507 / 1000000 : ℝ)) (c := (30189 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (3 / 128 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (76547 / 500000 : ℝ)) (c := (1733 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (3 / 256 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (54127 / 500000 : ℝ)) (c := (937 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (3 / 512 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (76547 / 1000000 : ℝ)) (c := (121 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (3 / 1024 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (54127 / 1000000 : ℝ)) (c := (57 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem driftSeries_le_2 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (3 / 32 : ℝ) ≤ (1253 / 10000 : ℝ) := by
  refine (driftSeries_split L (3 / 32 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (3 / 64 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (216507 / 1000000 : ℝ)) (c := (11919 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (3 / 128 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (76547 / 500000 : ℝ)) (c := (10871 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (3 / 256 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (54127 / 500000 : ℝ)) (c := (5393 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (3 / 512 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (76547 / 1000000 : ℝ)) (c := (49 / 31250 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (3 / 1024 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (54127 / 1000000 : ℝ)) (c := (107 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (3 / 2048 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (19137 / 500000 : ℝ)) (c := (21 / 100000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem driftSeries_le_3 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (3 / 64 : ℝ) ≤ (19253 / 200000 : ℝ) := by
  refine (driftSeries_split L (3 / 64 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (3 / 128 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (76547 / 500000 : ℝ)) (c := (1801 / 25000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (3 / 256 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (54127 / 500000 : ℝ)) (c := (8571 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (3 / 512 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (76547 / 1000000 : ℝ)) (c := (141 / 31250 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (3 / 1024 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (54127 / 1000000 : ℝ)) (c := (691 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (3 / 2048 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (19137 / 500000 : ℝ)) (c := (491 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (3 / 4096 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (3383 / 125000 : ℝ)) (c := (99 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem driftSeries_le_4 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (3 / 128 : ℝ) ≤ (79431 / 1000000 : ℝ) := by
  refine (driftSeries_split L (3 / 128 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (3 / 256 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (54127 / 500000 : ℝ)) (c := (29291 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (3 / 512 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (76547 / 1000000 : ℝ)) (c := (2891 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (3 / 1024 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (54127 / 1000000 : ℝ)) (c := (3977 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (3 / 2048 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (19137 / 500000 : ℝ)) (c := (253 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (3 / 4096 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (3383 / 125000 : ℝ)) (c := (231 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (3 / 8192 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (19137 / 1000000 : ℝ)) (c := (19 / 100000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

end DriftNumeric

section Link
open Real Uniform713

/-- The drift bounds of the cap-`2^L` classifier are at most the drift series at any
scale `Y ≥ cap L*d^2`. -/
theorem driftSum_le (L : ℕ) {d Y : ℝ} (hd : 0 < d) (hx : cap L * d ^ 2 ≤ Y) (hY : Y ≤ 3 / 8) :
    ∑ k ∈ range L, driftBound L k d ≤ ∑ J ∈ range L, driftTerm (J + 1) Y := by
  rw [← sum_range_reflect (fun k => driftBound L k d) L]
  apply sum_le_sum
  intro J hJ
  have hJL := mem_range.1 hJ
  set k := L - 1 - J with hk
  have hkL : k + (J + 1) = L := by omega
  have hc := cap_pos k
  have hratio : cap (k + (J + 1)) / cap k = 2 ^ (J + 1) := by
    simp only [cap, pow_add]
    field_simp
  set v := 1 + ((J + 1 : ℕ) : ℝ) * Real.log 2 with hv
  have hl := Real.log_two_gt_d9
  have hv1 : 1 ≤ v := by simp only [hv]; push_cast; nlinarith
  have ht : Tier2.Model.threshold1 (cap k) (cap L) = Real.sqrt (v / cap k) := by
    rw [← hkL]
    unfold Tier2.Model.threshold1
    rw [hratio, Real.log_pow]
  have hcapL : cap L = cap k * 2 ^ (J + 1) := by rw [← hkL]; simp only [cap, pow_add]
  have hyk : cap k * d ^ 2 ≤ Y / 2 ^ (J + 1) := by
    rw [le_div_iff₀ (by positivity)]
    rw [hcapL] at hx
    linarith
  have hY2 : Y / 2 ^ (J + 1) ≤ 3 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ≤ 2 ^ (J + 1) := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ J + 1 by omega)
      simpa using this
    nlinarith
  have hdt : d ≤ Tier2.Model.threshold1 (cap k) (cap L) := by
    rw [ht]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc]
    nlinarith
  have hexp : cap k * (Real.sqrt (v / cap k) - d) ^ 2 =
      (Real.sqrt v - Real.sqrt (cap k * d ^ 2)) ^ 2 := by
    have hs : Real.sqrt v = Real.sqrt (cap k) * Real.sqrt (v / cap k) := by
      rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq hd.le, hs]
    have hc' : Real.sqrt (cap k) ^ 2 = cap k := Real.sq_sqrt hc.le
    rw [show (Real.sqrt (cap k) * Real.sqrt (v / cap k) - Real.sqrt (cap k) * d) ^ 2 =
      Real.sqrt (cap k) ^ 2 * (Real.sqrt (v / cap k) - d) ^ 2 by ring, hc']
  have hsy : Real.sqrt (cap k * d ^ 2) ≤ Real.sqrt (Y / 2 ^ (J + 1)) := Real.sqrt_le_sqrt hyk
  have hsY : Real.sqrt (Y / 2 ^ (J + 1)) ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith)
  unfold driftBound driftTerm
  rw [ite_eq_left hdt, ht, mul_assoc, hexp]
  apply Real.exp_le_exp.2
  have h1 : (Real.sqrt v - Real.sqrt (Y / 2 ^ (J + 1))) ^ 2 ≤
      (Real.sqrt v - Real.sqrt (cap k * d ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [hv] at h1 ⊢
  push_cast at h1 ⊢
  linarith

end Link

end ThresholdHC.UpperSign
