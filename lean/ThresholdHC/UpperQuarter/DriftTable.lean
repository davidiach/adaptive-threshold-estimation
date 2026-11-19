import ThresholdHC.UpperQuarter.Drift

/-! Numerical drift tables for the four bands of the first grid point.

For the band `k` of `s`, with upper end `h_k`, the drift series at the scale
`h_k/2^(i+2)` is bounded for `i = 0, …, 4` by its first six terms, evaluated with
rational bounds and an eight-term Taylor sum, plus `1/2000`. The bounds were
chosen and checked in exact rational arithmetic by a script. -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2 ThresholdHC.UpperSign

section DriftTable
open Real Uniform713

theorem quarterSeries_le_0_0 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 64 : ℝ) ≤ (29883 / 125000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 64 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 128 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (96319 / 250000 : ℝ)) (c := (186839 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 256 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (17027 / 62500 : ℝ)) (c := (9993 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 512 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (96319 / 500000 : ℝ)) (c := (4319 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 1024 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (17027 / 125000 : ℝ)) (c := (1097 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 2048 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (96319 / 1000000 : ℝ)) (c := (27 / 40000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 4096 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (17027 / 250000 : ℝ)) (c := (123 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_0_1 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 128 : ℝ) ≤ (3917 / 25000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 128 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 256 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (17027 / 62500 : ℝ)) (c := (120609 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 512 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (96319 / 500000 : ℝ)) (c := (3339 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 1024 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (17027 / 125000 : ℝ)) (c := (1577 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 2048 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (96319 / 1000000 : ℝ)) (c := (219 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 4096 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (17027 / 250000 : ℝ)) (c := (289 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 8192 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (301 / 6250 : ℝ)) (c := (221 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_0_2 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 256 : ℝ) ≤ (113601 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 256 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 512 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (96319 / 500000 : ℝ)) (c := (85949 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 1024 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (17027 / 125000 : ℝ)) (c := (19891 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 2048 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (96319 / 1000000 : ℝ)) (c := (5043 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 4096 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (17027 / 250000 : ℝ)) (c := (299 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 8192 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (301 / 6250 : ℝ)) (c := (259 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 16384 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (17027 / 500000 : ℝ)) (c := (41 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_0_3 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 512 : ℝ) ≤ (44797 / 500000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 512 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 1024 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (17027 / 125000 : ℝ)) (c := (66699 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 2048 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (96319 / 1000000 : ℝ)) (c := (201 / 12500 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 4096 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (17027 / 250000 : ℝ)) (c := (4303 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 8192 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (301 / 6250 : ℝ)) (c := (1337 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 16384 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (17027 / 500000 : ℝ)) (c := (3 / 6250 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 32768 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (301 / 12500 : ℝ)) (c := (39 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_0_4 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 1024 : ℝ) ≤ (75413 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 1024 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 2048 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (96319 / 1000000 : ℝ)) (c := (55381 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 4096 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (17027 / 250000 : ℝ)) (c := (1381 / 100000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 8192 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (301 / 6250 : ℝ)) (c := (769 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 16384 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (17027 / 500000 : ℝ)) (c := (247 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 32768 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (301 / 12500 : ℝ)) (c := (227 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 65536 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (17027 / 1000000 : ℝ)) (c := (47 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_1_0 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (57 / 160 : ℝ) ≤ (271967 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (57 / 160 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (57 / 320 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (422049 / 1000000 : ℝ)) (c := (26647 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (57 / 640 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (149217 / 500000 : ℝ)) (c := (45403 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (57 / 1280 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (8441 / 40000 : ℝ)) (c := (4781 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (57 / 2560 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (149217 / 1000000 : ℝ)) (c := (2361 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (57 / 5120 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (105513 / 1000000 : ℝ)) (c := (71 / 100000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (57 / 10240 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (74609 / 1000000 : ℝ)) (c := (51 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_1_1 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (57 / 320 : ℝ) ≤ (21663 / 125000 : ℝ) := by
  refine (driftSeries_split_half L (57 / 320 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (57 / 640 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (149217 / 500000 : ℝ)) (c := (16749 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (57 / 1280 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (8441 / 40000 : ℝ)) (c := (29357 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (57 / 2560 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (149217 / 1000000 : ℝ)) (c := (106 / 15625 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (57 / 5120 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (105513 / 1000000 : ℝ)) (c := (369 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (57 / 10240 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (74609 / 1000000 : ℝ)) (c := (599 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (57 / 20480 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (52757 / 1000000 : ℝ)) (c := (227 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_1_2 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (57 / 640 : ℝ) ≤ (3829 / 31250 : ℝ) := by
  refine (driftSeries_split_half L (57 / 640 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (57 / 1280 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (8441 / 40000 : ℝ)) (c := (93123 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (57 / 2560 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (149217 / 1000000 : ℝ)) (c := (21303 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (57 / 5120 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (105513 / 1000000 : ℝ)) (c := (5311 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (57 / 10240 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (74609 / 1000000 : ℝ)) (c := (1551 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (57 / 20480 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (52757 / 1000000 : ℝ)) (c := (531 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (57 / 40960 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (7461 / 200000 : ℝ)) (c := (209 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_1_3 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (57 / 1280 : ℝ) ≤ (18939 / 200000 : ℝ) := by
  refine (driftSeries_split_half L (57 / 1280 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (57 / 2560 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (149217 / 1000000 : ℝ)) (c := (70783 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (57 / 5120 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (105513 / 1000000 : ℝ)) (c := (16893 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (57 / 10240 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (74609 / 1000000 : ℝ)) (c := (4463 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (57 / 20480 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (52757 / 1000000 : ℝ)) (c := (1371 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (57 / 40960 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (7461 / 200000 : ℝ)) (c := (61 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (57 / 81920 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (26379 / 1000000 : ℝ)) (c := (197 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_1_4 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (57 / 2560 : ℝ) ≤ (78491 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (57 / 2560 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (57 / 5120 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (105513 / 1000000 : ℝ)) (c := (28917 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (57 / 10240 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (74609 / 1000000 : ℝ)) (c := (447 / 31250 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (57 / 20480 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (52757 / 1000000 : ℝ)) (c := (1973 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (57 / 40960 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (7461 / 200000 : ℝ)) (c := (629 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (57 / 81920 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (26379 / 1000000 : ℝ)) (c := (23 / 50000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (57 / 163840 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (18653 / 1000000 : ℝ)) (c := (189 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_2_0 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (133 / 320 : ℝ) ≤ (19063 / 62500 : ℝ) := by
  refine (driftSeries_split_half L (133 / 320 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (133 / 640 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (91173 / 200000 : ℝ)) (c := (239527 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (133 / 1280 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (64469 / 200000 : ℝ)) (c := (6369 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (133 / 2560 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (227933 / 1000000 : ℝ)) (c := (164 / 15625 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (133 / 5120 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (161173 / 1000000 : ℝ)) (c := (1263 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (133 / 10240 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (113967 / 1000000 : ℝ)) (c := (93 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (133 / 20480 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (80587 / 1000000 : ℝ)) (c := (263 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_2_1 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (133 / 640 : ℝ) ≤ (189799 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (133 / 640 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (133 / 1280 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (64469 / 200000 : ℝ)) (c := (147267 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (133 / 2560 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (227933 / 1000000 : ℝ)) (c := (15997 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (133 / 5120 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (161173 / 1000000 : ℝ)) (c := (1813 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (133 / 10240 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (113967 / 1000000 : ℝ)) (c := (387 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (133 / 20480 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (80587 / 1000000 : ℝ)) (c := (619 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (133 / 40960 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (7123 / 125000 : ℝ)) (c := (29 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_2_2 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (133 / 1280 : ℝ) ≤ (131249 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (133 / 1280 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (133 / 2560 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (227933 / 1000000 : ℝ)) (c := (100137 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (133 / 5120 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (161173 / 1000000 : ℝ)) (c := (22683 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (133 / 10240 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (113967 / 1000000 : ℝ)) (c := (5569 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (133 / 20480 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (80587 / 1000000 : ℝ)) (c := (401 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (133 / 40960 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (7123 / 125000 : ℝ)) (c := (17 / 31250 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (133 / 81920 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (20147 / 500000 : ℝ)) (c := (53 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_2_3 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (133 / 2560 : ℝ) ≤ (12451 / 125000 : ℝ) := by
  refine (driftSeries_split_half L (133 / 2560 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (133 / 5120 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (161173 / 1000000 : ℝ)) (c := (74719 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (133 / 10240 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (113967 / 1000000 : ℝ)) (c := (8837 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (133 / 20480 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (80587 / 1000000 : ℝ)) (c := (577 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (133 / 40960 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (7123 / 125000 : ℝ)) (c := (351 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (133 / 81920 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (20147 / 500000 : ℝ)) (c := (31 / 62500 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (133 / 163840 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (7123 / 250000 : ℝ)) (c := (199 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_2_4 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (133 / 5120 : ℝ) ≤ (81419 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (133 / 5120 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (133 / 10240 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (113967 / 1000000 : ℝ)) (c := (60169 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (133 / 20480 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (80587 / 1000000 : ℝ)) (c := (7387 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (133 / 40960 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (7123 / 125000 : ℝ)) (c := (4041 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (133 / 81920 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (20147 / 500000 : ℝ)) (c := (1279 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (133 / 163840 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (7123 / 250000 : ℝ)) (c := (93 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (133 / 327680 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (20147 / 1000000 : ℝ)) (c := (191 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_3_0 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 40 : ℝ) ≤ (67639 / 200000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 40 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 80 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (24367 / 50000 : ℝ)) (c := (53177 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 160 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (172301 / 500000 : ℝ)) (c := (56631 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 320 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (24367 / 100000 : ℝ)) (c := (5721 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 640 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (172301 / 1000000 : ℝ)) (c := (2689 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 1280 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (24367 / 200000 : ℝ)) (c := (777 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 2560 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (86151 / 1000000 : ℝ)) (c := (271 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_3_1 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 80 : ℝ) ≤ (206233 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 80 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 160 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (172301 / 500000 : ℝ)) (c := (160483 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 320 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (24367 / 100000 : ℝ)) (c := (34637 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 640 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (172301 / 1000000 : ℝ)) (c := (1543 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 1280 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (24367 / 200000 : ℝ)) (c := (2023 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 2560 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (86151 / 1000000 : ℝ)) (c := (319 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 5120 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (30459 / 500000 : ℝ)) (c := (237 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_3_2 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 160 : ℝ) ≤ (139823 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 160 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 320 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (24367 / 100000 : ℝ)) (c := (107037 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 640 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (172301 / 1000000 : ℝ)) (c := (601 / 25000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 1280 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (24367 / 200000 : ℝ)) (c := (291 / 50000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 2560 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (86151 / 1000000 : ℝ)) (c := (331 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 5120 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (30459 / 500000 : ℝ)) (c := (139 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 10240 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (10769 / 250000 : ℝ)) (c := (43 / 200000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_3_3 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 320 : ℝ) ≤ (104379 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 320 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 640 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (172301 / 1000000 : ℝ)) (c := (4909 / 62500 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 1280 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (24367 / 200000 : ℝ)) (c := (1843 / 100000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 2560 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (86151 / 1000000 : ℝ)) (c := (4763 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 5120 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (30459 / 500000 : ℝ)) (c := (359 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 10240 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (10769 / 250000 : ℝ)) (c := (63 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 20480 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (30459 / 1000000 : ℝ)) (c := (101 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

theorem quarterSeries_le_3_4 (L : ℕ) :
    ∑ J ∈ range L, driftTerm (J + 1) (19 / 640 : ℝ) ≤ (84231 / 1000000 : ℝ) := by
  refine (driftSeries_split_half L (19 / 640 : ℝ) (by norm_num)).trans ?_
  have t1 := drift_term_le (J := 1) (y := (19 / 1280 : ℝ)) (a := (1301209 / 1000000 : ℝ)) (b := (24367 / 200000 : ℝ)) (c := (31207 / 500000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t2 := drift_term_le (J := 2) (y := (19 / 2560 : ℝ)) (a := (1544763 / 1000000 : ℝ)) (b := (86151 / 1000000 : ℝ)) (c := (1903 / 125000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t3 := drift_term_le (J := 3) (y := (19 / 5120 : ℝ)) (a := (1754833 / 1000000 : ℝ)) (b := (30459 / 500000 : ℝ)) (c := (1033 / 250000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t4 := drift_term_le (J := 4) (y := (19 / 10240 : ℝ)) (a := (388463 / 200000 : ℝ)) (b := (10769 / 250000 : ℝ)) (c := (1299 / 1000000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t5 := drift_term_le (J := 5) (y := (19 / 20480 : ℝ)) (a := (528307 / 250000 : ℝ)) (b := (30459 / 1000000 : ℝ)) (c := (47 / 100000 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have t6 := drift_term_le (J := 6) (y := (19 / 40960 : ℝ)) (a := (2271317 / 1000000 : ℝ)) (b := (10769 / 500000 : ℝ)) (c := (3 / 15625 : ℝ))
    (by norm_num) (by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  simp only [driftTerm] at t1 t2 t3 t4 t5 t6 ⊢
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

end DriftTable

end ThresholdHC.UpperQuarter
