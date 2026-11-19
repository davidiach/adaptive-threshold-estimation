import ThresholdHC.UpperCost.Offset

/-! A sharper offset bound for the grids with level difference at least three.

The call-cost sum of `UpperCost` follows one dyadic grid for each difference
`j = l - k` of the level `l` and the check `k`, with threshold scale
`v = 1 + j*log 2`. `UpperCost.Offset` bounds the offset sum of these grids by
`89/20` for `j = 1` and by `17/4` for `j ≥ 2`. The offset sum decreases as `v`
grows; for `v ≥ 307/100`, which covers `j ≥ 3`, it is at most `399/100`. The
proof splits `[1, 2]` into 29 pieces, chosen and checked in exact rational
arithmetic by a script, and bounds the first four doubled terms on each piece
by monotonicity and a Taylor lower bound for the exponential, as in
`UpperCost.Offset`. -/
noncomputable section
namespace ThresholdHC.UpperCallCost
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork ThresholdHC.UpperCost

theorem far_piece_0 (s : ℝ) (hlo : (1 : ℝ) ≤ s) (hhi : s ≤ (103 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (103 / 100 : ℝ)) (h := (203 / 200 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (1 : ℝ)) (hi := (103 / 100 : ℝ)) (ρ := (1 : ℝ)) (h := (203 / 200 : ℝ)) (c := (203 / 200 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (2 : ℝ)) (hi := (103 / 50 : ℝ)) (ρ := (707 / 500 : ℝ)) (h := (359 / 250 : ℝ)) (c := (251 / 500 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (4 : ℝ)) (hi := (103 / 25 : ℝ)) (ρ := (2 : ℝ)) (h := (203 / 100 : ℝ)) (c := (7 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (8 : ℝ)) (hi := (206 / 25 : ℝ)) (ρ := (707 / 250 : ℝ)) (h := (2871 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_1 (s : ℝ) (hlo : (103 / 100 : ℝ) ≤ s) (hhi : s ≤ (211 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (211 / 200 : ℝ)) (h := (257 / 250 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (103 / 100 : ℝ)) (hi := (211 / 200 : ℝ)) (ρ := (507 / 500 : ℝ)) (h := (257 / 250 : ℝ)) (c := (1027 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (103 / 50 : ℝ)) (hi := (211 / 100 : ℝ)) (ρ := (287 / 200 : ℝ)) (h := (1453 / 1000 : ℝ)) (c := (91 / 200 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (103 / 25 : ℝ)) (hi := (211 / 50 : ℝ)) (ρ := (2029 / 1000 : ℝ)) (h := (411 / 200 : ℝ)) (c := (1 / 200 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (206 / 25 : ℝ)) (hi := (211 / 25 : ℝ)) (ρ := (287 / 100 : ℝ)) (h := (1453 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_2 (s : ℝ) (hlo : (211 / 200 : ℝ) ≤ s) (hhi : s ≤ (27 / 25 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (27 / 25 : ℝ)) (h := (26 / 25 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (211 / 200 : ℝ)) (hi := (27 / 25 : ℝ)) (ρ := (1027 / 1000 : ℝ)) (h := (26 / 25 : ℝ)) (c := (259 / 250 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (211 / 100 : ℝ)) (hi := (54 / 25 : ℝ)) (ρ := (363 / 250 : ℝ)) (h := (147 / 100 : ℝ)) (c := (21 / 50 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (211 / 50 : ℝ)) (hi := (108 / 25 : ℝ)) (ρ := (1027 / 500 : ℝ)) (h := (2079 / 1000 : ℝ)) (c := (1 / 250 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (211 / 25 : ℝ)) (hi := (216 / 25 : ℝ)) (ρ := (581 / 200 : ℝ)) (h := (147 / 50 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_3 (s : ℝ) (hlo : (27 / 25 : ℝ) ≤ s) (hhi : s ≤ (221 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (221 / 200 : ℝ)) (h := (263 / 250 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (27 / 25 : ℝ)) (hi := (221 / 200 : ℝ)) (ρ := (1039 / 1000 : ℝ)) (h := (263 / 250 : ℝ)) (c := (1043 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (54 / 25 : ℝ)) (hi := (221 / 100 : ℝ)) (ρ := (1469 / 1000 : ℝ)) (h := (1487 / 1000 : ℝ)) (c := (193 / 500 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (108 / 25 : ℝ)) (hi := (221 / 50 : ℝ)) (ρ := (1039 / 500 : ℝ)) (h := (2103 / 1000 : ℝ)) (c := (3 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (216 / 25 : ℝ)) (hi := (221 / 25 : ℝ)) (ρ := (2939 / 1000 : ℝ)) (h := (1487 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_4 (s : ℝ) (hlo : (221 / 200 : ℝ) ≤ s) (hhi : s ≤ (113 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (113 / 100 : ℝ)) (h := (133 / 125 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (221 / 200 : ℝ)) (hi := (113 / 100 : ℝ)) (ρ := (1051 / 1000 : ℝ)) (h := (133 / 125 : ℝ)) (c := (131 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (221 / 100 : ℝ)) (hi := (113 / 50 : ℝ)) (ρ := (743 / 500 : ℝ)) (h := (188 / 125 : ℝ)) (c := (353 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (221 / 50 : ℝ)) (hi := (113 / 25 : ℝ)) (ρ := (1051 / 500 : ℝ)) (h := (2127 / 1000 : ℝ)) (c := (3 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (221 / 25 : ℝ)) (hi := (226 / 25 : ℝ)) (ρ := (2973 / 1000 : ℝ)) (h := (3007 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_5 (s : ℝ) (hlo : (113 / 100 : ℝ) ≤ s) (hhi : s ≤ (231 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (231 / 200 : ℝ)) (h := (43 / 40 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (113 / 100 : ℝ)) (hi := (231 / 200 : ℝ)) (ρ := (1063 / 1000 : ℝ)) (h := (43 / 40 : ℝ)) (c := (21 / 20 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (113 / 50 : ℝ)) (hi := (231 / 100 : ℝ)) (ρ := (1503 / 1000 : ℝ)) (h := (38 / 25 : ℝ)) (c := (161 / 500 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (113 / 25 : ℝ)) (hi := (231 / 50 : ℝ)) (ρ := (1063 / 500 : ℝ)) (h := (43 / 20 : ℝ)) (c := (1 / 500 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (226 / 25 : ℝ)) (hi := (231 / 25 : ℝ)) (ρ := (1503 / 500 : ℝ)) (h := (76 / 25 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_6 (s : ℝ) (hlo : (231 / 200 : ℝ) ≤ s) (hhi : s ≤ (59 / 50 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (59 / 50 : ℝ)) (h := (1087 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (231 / 200 : ℝ)) (hi := (59 / 50 : ℝ)) (ρ := (537 / 500 : ℝ)) (h := (1087 / 1000 : ℝ)) (c := (263 / 250 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (231 / 100 : ℝ)) (hi := (59 / 25 : ℝ)) (ρ := (1519 / 1000 : ℝ)) (h := (1537 / 1000 : ℝ)) (c := (59 / 200 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (231 / 50 : ℝ)) (hi := (118 / 25 : ℝ)) (ρ := (2149 / 1000 : ℝ)) (h := (2173 / 1000 : ℝ)) (c := (1 / 500 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (231 / 25 : ℝ)) (hi := (236 / 25 : ℝ)) (ρ := (3039 / 1000 : ℝ)) (h := (3073 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_7 (s : ℝ) (hlo : (59 / 50 : ℝ) ≤ s) (hhi : s ≤ (241 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (241 / 200 : ℝ)) (h := (549 / 500 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (59 / 50 : ℝ)) (hi := (241 / 200 : ℝ)) (ρ := (543 / 500 : ℝ)) (h := (549 / 500 : ℝ)) (c := (21 / 20 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (59 / 25 : ℝ)) (hi := (241 / 100 : ℝ)) (ρ := (192 / 125 : ℝ)) (h := (1553 / 1000 : ℝ)) (c := (267 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (118 / 25 : ℝ)) (hi := (241 / 50 : ℝ)) (ρ := (543 / 250 : ℝ)) (h := (549 / 250 : ℝ)) (c := (1 / 500 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (236 / 25 : ℝ)) (hi := (241 / 25 : ℝ)) (ρ := (384 / 125 : ℝ)) (h := (621 / 200 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_8 (s : ℝ) (hlo : (241 / 200 : ℝ) ≤ s) (hhi : s ≤ (123 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (123 / 100 : ℝ)) (h := (111 / 100 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (241 / 200 : ℝ)) (hi := (123 / 100 : ℝ)) (ρ := (1097 / 1000 : ℝ)) (h := (111 / 100 : ℝ)) (c := (131 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (241 / 100 : ℝ)) (hi := (123 / 50 : ℝ)) (ρ := (194 / 125 : ℝ)) (h := (1569 / 1000 : ℝ)) (c := (121 / 500 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (241 / 50 : ℝ)) (hi := (123 / 25 : ℝ)) (ρ := (439 / 200 : ℝ)) (h := (2219 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (241 / 25 : ℝ)) (hi := (246 / 25 : ℝ)) (ρ := (388 / 125 : ℝ)) (h := (3137 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_9 (s : ℝ) (hlo : (123 / 100 : ℝ) ≤ s) (hhi : s ≤ (63 / 50 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (63 / 50 : ℝ)) (h := (1123 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (123 / 100 : ℝ)) (hi := (63 / 50 : ℝ)) (ρ := (1109 / 1000 : ℝ)) (h := (1123 / 1000 : ℝ)) (c := (261 / 250 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (123 / 50 : ℝ)) (hi := (63 / 25 : ℝ)) (ρ := (196 / 125 : ℝ)) (h := (397 / 250 : ℝ)) (c := (11 / 50 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (123 / 25 : ℝ)) (hi := (126 / 25 : ℝ)) (ρ := (1109 / 500 : ℝ)) (h := (449 / 200 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (246 / 25 : ℝ)) (hi := (252 / 25 : ℝ)) (ρ := (392 / 125 : ℝ)) (h := (127 / 40 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_10 (s : ℝ) (hlo : (63 / 50 : ℝ) ≤ s) (hhi : s ≤ (129 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (129 / 100 : ℝ)) (h := (142 / 125 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (63 / 50 : ℝ)) (hi := (129 / 100 : ℝ)) (ρ := (561 / 500 : ℝ)) (h := (142 / 125 : ℝ)) (c := (1037 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (63 / 25 : ℝ)) (hi := (129 / 50 : ℝ)) (ρ := (1587 / 1000 : ℝ)) (h := (1607 / 1000 : ℝ)) (c := (39 / 200 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (126 / 25 : ℝ)) (hi := (129 / 25 : ℝ)) (ρ := (561 / 250 : ℝ)) (h := (284 / 125 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (252 / 25 : ℝ)) (hi := (258 / 25 : ℝ)) (ρ := (1587 / 500 : ℝ)) (h := (3213 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_11 (s : ℝ) (hlo : (129 / 100 : ℝ) ≤ s) (hhi : s ≤ (33 / 25 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (33 / 25 : ℝ)) (h := (1149 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (129 / 100 : ℝ)) (hi := (33 / 25 : ℝ)) (ρ := (227 / 200 : ℝ)) (h := (1149 / 1000 : ℝ)) (c := (257 / 250 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (129 / 50 : ℝ)) (hi := (66 / 25 : ℝ)) (ρ := (803 / 500 : ℝ)) (h := (13 / 8 : ℝ)) (c := (171 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (129 / 25 : ℝ)) (hi := (132 / 25 : ℝ)) (ρ := (2271 / 1000 : ℝ)) (h := (1149 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (258 / 25 : ℝ)) (hi := (264 / 25 : ℝ)) (ρ := (803 / 250 : ℝ)) (h := (13 / 4 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_12 (s : ℝ) (hlo : (33 / 25 : ℝ) ≤ s) (hhi : s ≤ (27 / 20 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (27 / 20 : ℝ)) (h := (581 / 500 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (33 / 25 : ℝ)) (hi := (27 / 20 : ℝ)) (ρ := (287 / 250 : ℝ)) (h := (581 / 500 : ℝ)) (c := (127 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (66 / 25 : ℝ)) (hi := (27 / 10 : ℝ)) (ρ := (203 / 125 : ℝ)) (h := (411 / 250 : ℝ)) (c := (19 / 125 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (132 / 25 : ℝ)) (hi := (27 / 5 : ℝ)) (ρ := (2297 / 1000 : ℝ)) (h := (581 / 250 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (264 / 25 : ℝ)) (hi := (54 / 5 : ℝ)) (ρ := (3249 / 1000 : ℝ)) (h := (3287 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_13 (s : ℝ) (hlo : (27 / 20 : ℝ) ≤ s) (hhi : s ≤ (69 / 50 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (69 / 50 : ℝ)) (h := (47 / 40 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (27 / 20 : ℝ)) (hi := (69 / 50 : ℝ)) (ρ := (1161 / 1000 : ℝ)) (h := (47 / 40 : ℝ)) (c := (1003 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (27 / 10 : ℝ)) (hi := (69 / 25 : ℝ)) (ρ := (1643 / 1000 : ℝ)) (h := (831 / 500 : ℝ)) (c := (33 / 250 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (27 / 5 : ℝ)) (hi := (138 / 25 : ℝ)) (ρ := (2323 / 1000 : ℝ)) (h := (47 / 20 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (54 / 5 : ℝ)) (hi := (276 / 25 : ℝ)) (ρ := (1643 / 500 : ℝ)) (h := (3323 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_14 (s : ℝ) (hlo : (69 / 50 : ℝ) ≤ s) (hhi : s ≤ (141 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (141 / 100 : ℝ)) (h := (297 / 250 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (69 / 50 : ℝ)) (hi := (141 / 100 : ℝ)) (ρ := (587 / 500 : ℝ)) (h := (297 / 250 : ℝ)) (c := (987 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (69 / 25 : ℝ)) (hi := (141 / 50 : ℝ)) (ρ := (1661 / 1000 : ℝ)) (h := (42 / 25 : ℝ)) (c := (29 / 250 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (138 / 25 : ℝ)) (hi := (141 / 25 : ℝ)) (ρ := (2349 / 1000 : ℝ)) (h := (19 / 8 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (276 / 25 : ℝ)) (hi := (282 / 25 : ℝ)) (ρ := (1661 / 500 : ℝ)) (h := (3359 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_15 (s : ℝ) (hlo : (141 / 100 : ℝ) ≤ s) (hhi : s ≤ (36 / 25 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (36 / 25 : ℝ)) (h := (6 / 5 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (141 / 100 : ℝ)) (hi := (36 / 25 : ℝ)) (ρ := (1187 / 1000 : ℝ)) (h := (6 / 5 : ℝ)) (c := (969 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (141 / 50 : ℝ)) (hi := (72 / 25 : ℝ)) (ρ := (1679 / 1000 : ℝ)) (h := (849 / 500 : ℝ)) (c := (101 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (141 / 25 : ℝ)) (hi := (144 / 25 : ℝ)) (ρ := (1187 / 500 : ℝ)) (h := (12 / 5 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (282 / 25 : ℝ)) (hi := (288 / 25 : ℝ)) (ρ := (1679 / 500 : ℝ)) (h := (679 / 200 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_16 (s : ℝ) (hlo : (36 / 25 : ℝ) ≤ s) (hhi : s ≤ (59 / 40 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (59 / 40 : ℝ)) (h := (243 / 200 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (36 / 25 : ℝ)) (hi := (59 / 40 : ℝ)) (ρ := (6 / 5 : ℝ)) (h := (243 / 200 : ℝ)) (c := (951 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (72 / 25 : ℝ)) (hi := (59 / 20 : ℝ)) (ρ := (1697 / 1000 : ℝ)) (h := (859 / 500 : ℝ)) (c := (89 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (144 / 25 : ℝ)) (hi := (59 / 10 : ℝ)) (ρ := (12 / 5 : ℝ)) (h := (2429 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (288 / 25 : ℝ)) (hi := (59 / 5 : ℝ)) (ρ := (1697 / 500 : ℝ)) (h := (859 / 250 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_17 (s : ℝ) (hlo : (59 / 40 : ℝ) ≤ s) (hhi : s ≤ (151 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (151 / 100 : ℝ)) (h := (1229 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (59 / 40 : ℝ)) (hi := (151 / 100 : ℝ)) (ρ := (607 / 500 : ℝ)) (h := (1229 / 1000 : ℝ)) (c := (116 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (59 / 20 : ℝ)) (hi := (151 / 50 : ℝ)) (ρ := (1717 / 1000 : ℝ)) (h := (869 / 500 : ℝ)) (c := (19 / 250 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (59 / 10 : ℝ)) (hi := (151 / 25 : ℝ)) (ρ := (607 / 250 : ℝ)) (h := (1229 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (59 / 5 : ℝ)) (hi := (302 / 25 : ℝ)) (ρ := (687 / 200 : ℝ)) (h := (869 / 250 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_18 (s : ℝ) (hlo : (151 / 100 : ℝ) ≤ s) (hhi : s ≤ (309 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (309 / 200 : ℝ)) (h := (1243 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (151 / 100 : ℝ)) (hi := (309 / 200 : ℝ)) (ρ := (307 / 250 : ℝ)) (h := (1243 / 1000 : ℝ)) (c := (113 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (151 / 50 : ℝ)) (hi := (309 / 100 : ℝ)) (ρ := (1737 / 1000 : ℝ)) (h := (879 / 500 : ℝ)) (c := (8 / 125 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (151 / 25 : ℝ)) (hi := (309 / 50 : ℝ)) (ρ := (2457 / 1000 : ℝ)) (h := (1243 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (302 / 25 : ℝ)) (hi := (309 / 25 : ℝ)) (ρ := (139 / 40 : ℝ)) (h := (879 / 250 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_19 (s : ℝ) (hlo : (309 / 200 : ℝ) ≤ s) (hhi : s ≤ (317 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (317 / 200 : ℝ)) (h := (1259 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (309 / 200 : ℝ)) (hi := (317 / 200 : ℝ)) (ρ := (621 / 500 : ℝ)) (h := (1259 / 1000 : ℝ)) (c := (879 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (309 / 100 : ℝ)) (hi := (317 / 100 : ℝ)) (ρ := (1757 / 1000 : ℝ)) (h := (1781 / 1000 : ℝ)) (c := (11 / 200 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (309 / 50 : ℝ)) (hi := (317 / 50 : ℝ)) (ρ := (497 / 200 : ℝ)) (h := (1259 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (309 / 25 : ℝ)) (hi := (317 / 25 : ℝ)) (ρ := (703 / 200 : ℝ)) (h := (3561 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_20 (s : ℝ) (hlo : (317 / 200 : ℝ) ≤ s) (hhi : s ≤ (13 / 8 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (13 / 8 : ℝ)) (h := (51 / 40 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (317 / 200 : ℝ)) (hi := (13 / 8 : ℝ)) (ρ := (629 / 500 : ℝ)) (h := (51 / 40 : ℝ)) (c := (106 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (317 / 100 : ℝ)) (hi := (13 / 4 : ℝ)) (ρ := (89 / 50 : ℝ)) (h := (1803 / 1000 : ℝ)) (c := (9 / 200 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (317 / 50 : ℝ)) (hi := (13 / 2 : ℝ)) (ρ := (2517 / 1000 : ℝ)) (h := (51 / 20 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (317 / 25 : ℝ)) (hi := (13 : ℝ)) (ρ := (89 / 25 : ℝ)) (h := (1803 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_21 (s : ℝ) (hlo : (13 / 8 : ℝ) ≤ s) (hhi : s ≤ (333 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (333 / 200 : ℝ)) (h := (1291 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (13 / 8 : ℝ)) (hi := (333 / 200 : ℝ)) (ρ := (637 / 500 : ℝ)) (h := (1291 / 1000 : ℝ)) (c := (163 / 200 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (13 / 4 : ℝ)) (hi := (333 / 100 : ℝ)) (ρ := (901 / 500 : ℝ)) (h := (73 / 40 : ℝ)) (c := (37 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (13 / 2 : ℝ)) (hi := (333 / 50 : ℝ)) (ρ := (2549 / 1000 : ℝ)) (h := (2581 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (13 : ℝ)) (hi := (333 / 25 : ℝ)) (ρ := (721 / 200 : ℝ)) (h := (73 / 20 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_22 (s : ℝ) (hlo : (333 / 200 : ℝ) ≤ s) (hhi : s ≤ (171 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (171 / 100 : ℝ)) (h := (327 / 250 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (333 / 200 : ℝ)) (hi := (171 / 100 : ℝ)) (ρ := (129 / 100 : ℝ)) (h := (327 / 250 : ℝ)) (c := (781 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (333 / 100 : ℝ)) (hi := (171 / 50 : ℝ)) (ρ := (228 / 125 : ℝ)) (h := (37 / 20 : ℝ)) (c := (31 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (333 / 50 : ℝ)) (hi := (171 / 25 : ℝ)) (ρ := (129 / 50 : ℝ)) (h := (327 / 125 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (333 / 25 : ℝ)) (hi := (342 / 25 : ℝ)) (ρ := (3649 / 1000 : ℝ)) (h := (3699 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_23 (s : ℝ) (hlo : (171 / 100 : ℝ) ≤ s) (hhi : s ≤ (44 / 25 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (44 / 25 : ℝ)) (h := (1327 / 1000 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (171 / 100 : ℝ)) (hi := (44 / 25 : ℝ)) (ρ := (1307 / 1000 : ℝ)) (h := (1327 / 1000 : ℝ)) (c := (93 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (171 / 50 : ℝ)) (hi := (88 / 25 : ℝ)) (ρ := (1849 / 1000 : ℝ)) (h := (1877 / 1000 : ℝ)) (c := (1 / 40 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (171 / 25 : ℝ)) (hi := (176 / 25 : ℝ)) (ρ := (523 / 200 : ℝ)) (h := (1327 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (342 / 25 : ℝ)) (hi := (352 / 25 : ℝ)) (ρ := (1849 / 500 : ℝ)) (h := (3753 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_24 (s : ℝ) (hlo : (44 / 25 : ℝ) ≤ s) (hhi : s ≤ (181 / 100 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (181 / 100 : ℝ)) (h := (673 / 500 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (44 / 25 : ℝ)) (hi := (181 / 100 : ℝ)) (ρ := (663 / 500 : ℝ)) (h := (673 / 500 : ℝ)) (c := (701 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (88 / 25 : ℝ)) (hi := (181 / 50 : ℝ)) (ρ := (469 / 250 : ℝ)) (h := (1903 / 1000 : ℝ)) (c := (1 / 50 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (176 / 25 : ℝ)) (hi := (181 / 25 : ℝ)) (ρ := (2653 / 1000 : ℝ)) (h := (2691 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (352 / 25 : ℝ)) (hi := (362 / 25 : ℝ)) (ρ := (469 / 125 : ℝ)) (h := (1903 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_25 (s : ℝ) (hlo : (181 / 100 : ℝ) ≤ s) (hhi : s ≤ (373 / 200 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (373 / 200 : ℝ)) (h := (683 / 500 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (181 / 100 : ℝ)) (hi := (373 / 200 : ℝ)) (ρ := (269 / 200 : ℝ)) (h := (683 / 500 : ℝ)) (c := (329 / 500 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (181 / 50 : ℝ)) (hi := (373 / 100 : ℝ)) (ρ := (951 / 500 : ℝ)) (h := (483 / 250 : ℝ)) (c := (2 / 125 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (181 / 25 : ℝ)) (hi := (373 / 50 : ℝ)) (ρ := (269 / 100 : ℝ)) (h := (683 / 250 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (362 / 25 : ℝ)) (hi := (373 / 25 : ℝ)) (ρ := (761 / 200 : ℝ)) (h := (3863 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_26 (s : ℝ) (hlo : (373 / 200 : ℝ) ≤ s) (hhi : s ≤ (48 / 25 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (48 / 25 : ℝ)) (h := (693 / 500 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (373 / 200 : ℝ)) (hi := (48 / 25 : ℝ)) (ρ := (273 / 200 : ℝ)) (h := (693 / 500 : ℝ)) (c := (153 / 250 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (373 / 100 : ℝ)) (hi := (96 / 25 : ℝ)) (ρ := (1931 / 1000 : ℝ)) (h := (49 / 25 : ℝ)) (c := (3 / 250 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (373 / 50 : ℝ)) (hi := (192 / 25 : ℝ)) (ρ := (2731 / 1000 : ℝ)) (h := (693 / 250 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (373 / 25 : ℝ)) (hi := (384 / 25 : ℝ)) (ρ := (1931 / 500 : ℝ)) (h := (98 / 25 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_27 (s : ℝ) (hlo : (48 / 25 : ℝ) ≤ s) (hhi : s ≤ (99 / 50 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (99 / 50 : ℝ)) (h := (176 / 125 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (48 / 25 : ℝ)) (hi := (99 / 50 : ℝ)) (ρ := (277 / 200 : ℝ)) (h := (176 / 125 : ℝ)) (c := (567 / 1000 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (96 / 25 : ℝ)) (hi := (99 / 25 : ℝ)) (ρ := (1959 / 1000 : ℝ)) (h := (199 / 100 : ℝ)) (c := (9 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (192 / 25 : ℝ)) (hi := (198 / 25 : ℝ)) (ρ := (2771 / 1000 : ℝ)) (h := (563 / 200 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (384 / 25 : ℝ)) (hi := (396 / 25 : ℝ)) (ρ := (3919 / 1000 : ℝ)) (h := (199 / 50 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

theorem far_piece_28 (s : ℝ) (hlo : (99 / 50 : ℝ) ≤ s) (hhi : s ≤ (2 : ℝ)) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 ≤
      (399 / 100 : ℝ) := by
  have e := base_le (s := s) (b := (2 : ℝ)) (h := (283 / 200 : ℝ)) hhi (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := s) (lo := (99 / 50 : ℝ)) (hi := (2 : ℝ)) (ρ := (1407 / 1000 : ℝ)) (h := (283 / 200 : ℝ)) (c := (64 / 125 : ℝ))
    hv (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 2 * s) (lo := (99 / 25 : ℝ)) (hi := (4 : ℝ)) (ρ := (1989 / 1000 : ℝ)) (h := (2 : ℝ)) (c := (7 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 4 * s) (lo := (198 / 25 : ℝ)) (hi := (8 : ℝ)) (ρ := (1407 / 500 : ℝ)) (h := (2829 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (307 / 100 : ℝ)) (t := 8 * s) (lo := (396 / 25 : ℝ)) (hi := (16 : ℝ)) (ρ := (3979 / 1000 : ℝ)) (h := (4 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

/-- The offset sum for `v ≥ 307/100`, which covers `v = 1 + j*log 2` for `j ≥ 3`. -/
theorem offset_le_far (s : ℝ) (h1 : 1 ≤ s) (h2 : s ≤ 2) {v : ℝ} (hv : (307 / 100 : ℝ) ≤ v) (I : ℕ) :
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ range I, tailTerm v (2 ^ i * s) ≤ (399 / 100 : ℝ) := by
  have hv1 : 1 ≤ v := le_trans (by norm_num) hv
  refine (offset_reduce s h1 hv1 I).trans ?_
  rcases le_or_gt s (103 / 100 : ℝ) with hk | hp
  · exact far_piece_0 s h1 hk hv
  rcases le_or_gt s (211 / 200 : ℝ) with hk | hp
  · exact far_piece_1 s hp.le hk hv
  rcases le_or_gt s (27 / 25 : ℝ) with hk | hp
  · exact far_piece_2 s hp.le hk hv
  rcases le_or_gt s (221 / 200 : ℝ) with hk | hp
  · exact far_piece_3 s hp.le hk hv
  rcases le_or_gt s (113 / 100 : ℝ) with hk | hp
  · exact far_piece_4 s hp.le hk hv
  rcases le_or_gt s (231 / 200 : ℝ) with hk | hp
  · exact far_piece_5 s hp.le hk hv
  rcases le_or_gt s (59 / 50 : ℝ) with hk | hp
  · exact far_piece_6 s hp.le hk hv
  rcases le_or_gt s (241 / 200 : ℝ) with hk | hp
  · exact far_piece_7 s hp.le hk hv
  rcases le_or_gt s (123 / 100 : ℝ) with hk | hp
  · exact far_piece_8 s hp.le hk hv
  rcases le_or_gt s (63 / 50 : ℝ) with hk | hp
  · exact far_piece_9 s hp.le hk hv
  rcases le_or_gt s (129 / 100 : ℝ) with hk | hp
  · exact far_piece_10 s hp.le hk hv
  rcases le_or_gt s (33 / 25 : ℝ) with hk | hp
  · exact far_piece_11 s hp.le hk hv
  rcases le_or_gt s (27 / 20 : ℝ) with hk | hp
  · exact far_piece_12 s hp.le hk hv
  rcases le_or_gt s (69 / 50 : ℝ) with hk | hp
  · exact far_piece_13 s hp.le hk hv
  rcases le_or_gt s (141 / 100 : ℝ) with hk | hp
  · exact far_piece_14 s hp.le hk hv
  rcases le_or_gt s (36 / 25 : ℝ) with hk | hp
  · exact far_piece_15 s hp.le hk hv
  rcases le_or_gt s (59 / 40 : ℝ) with hk | hp
  · exact far_piece_16 s hp.le hk hv
  rcases le_or_gt s (151 / 100 : ℝ) with hk | hp
  · exact far_piece_17 s hp.le hk hv
  rcases le_or_gt s (309 / 200 : ℝ) with hk | hp
  · exact far_piece_18 s hp.le hk hv
  rcases le_or_gt s (317 / 200 : ℝ) with hk | hp
  · exact far_piece_19 s hp.le hk hv
  rcases le_or_gt s (13 / 8 : ℝ) with hk | hp
  · exact far_piece_20 s hp.le hk hv
  rcases le_or_gt s (333 / 200 : ℝ) with hk | hp
  · exact far_piece_21 s hp.le hk hv
  rcases le_or_gt s (171 / 100 : ℝ) with hk | hp
  · exact far_piece_22 s hp.le hk hv
  rcases le_or_gt s (44 / 25 : ℝ) with hk | hp
  · exact far_piece_23 s hp.le hk hv
  rcases le_or_gt s (181 / 100 : ℝ) with hk | hp
  · exact far_piece_24 s hp.le hk hv
  rcases le_or_gt s (373 / 200 : ℝ) with hk | hp
  · exact far_piece_25 s hp.le hk hv
  rcases le_or_gt s (48 / 25 : ℝ) with hk | hp
  · exact far_piece_26 s hp.le hk hv
  rcases le_or_gt s (99 / 50 : ℝ) with hk | hp
  · exact far_piece_27 s hp.le hk hv
  exact far_piece_28 s hp.le h2 hv

end ThresholdHC.UpperCallCost
