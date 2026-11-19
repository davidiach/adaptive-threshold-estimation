import ThresholdHC.UpperDisagreement.CapOffset

/-! The offset sum of the stage with the split at `3/4`.

Along the dyadic grid of levels, the levels below the split `3/4` contribute at
most `(1613/1000)*sqrt s` for the first grid point `s` in `[3/4, 3/2]`
(`Grid`), and the levels from `s` on contribute the cap terms
`capTerm (2^i*s)`. The offset bound `247/100` splits `[3/4, 3/2]` into pieces
and bounds the first six doubled cap terms on each piece by monotonicity and a
Taylor lower bound for the exponential. -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ProbabilityTheory Finset

section SignOffset
open Real Uniform713

theorem scaled_sqrt_le {A s b h : ℝ} (hA : 0 ≤ A) (hb : s ≤ b) (hh : 0 ≤ h) (hbh : b ≤ h ^ 2) :
    A * Real.sqrt s ≤ A * h := by
  have hs : Real.sqrt s ≤ h := by
    rw [Real.sqrt_le_left hh]
    linarith
  exact mul_le_mul_of_nonneg_left hs hA

/-- Keep the first six doubled cap terms; the rest add at most `1/1000`. -/
theorem sign_offset_reduce (s : ℝ) (h1 : 3 / 4 ≤ s) (I : ℕ) :
    (1613 / 1000 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤
      (1613 / 1000 : ℝ) * Real.sqrt s +
        (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) +
          UpperDisagreement.capTerm (4 * s) + UpperDisagreement.capTerm (8 * s) +
          UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 := by
  have h := UpperDisagreement.cap_offset_reduce s (by linarith) I
  linarith

theorem sign_piece_0 {s : ℝ} (ha : (3 / 4 : ℝ) ≤ s) (hb : s ≤ (153 / 200 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (153 / 200 : ℝ)) (h := (7 / 8 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (3 / 4 : ℝ)) (hi := (153 / 200 : ℝ)) (h := (7 / 8 : ℝ)) (e₁ := (22317 / 100000 : ℝ)) (e₂ := (47237 / 100000 : ℝ)) (c := (609 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (3 / 2 : ℝ)) (hi := (153 / 100 : ℝ)) (h := (1237 / 1000 : ℝ)) (e₁ := (5039 / 100000 : ℝ)) (e₂ := (22317 / 100000 : ℝ)) (c := (339 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (3 : ℝ)) (hi := (153 / 50 : ℝ)) (h := (7 / 4 : ℝ)) (e₁ := (167 / 50000 : ℝ)) (e₂ := (5039 / 100000 : ℝ)) (c := (19 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (6 : ℝ)) (hi := (153 / 25 : ℝ)) (h := (1237 / 500 : ℝ)) (e₁ := (7 / 100000 : ℝ)) (e₂ := (167 / 50000 : ℝ)) (c := (9 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (12 : ℝ)) (hi := (306 / 25 : ℝ)) (h := (3499 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (7 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (24 : ℝ)) (hi := (612 / 25 : ℝ)) (h := (1237 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_1 {s : ℝ} (ha : (153 / 200 : ℝ) ≤ s) (hb : s ≤ (157 / 200 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (157 / 200 : ℝ)) (h := (887 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (153 / 200 : ℝ)) (hi := (157 / 200 : ℝ)) (h := (887 / 1000 : ℝ)) (e₁ := (10829 / 50000 : ℝ)) (e₂ := (23267 / 50000 : ℝ)) (c := (121 / 200 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (153 / 100 : ℝ)) (hi := (157 / 100 : ℝ)) (h := (1253 / 1000 : ℝ)) (e₁ := (297 / 6250 : ℝ)) (e₂ := (10829 / 50000 : ℝ)) (c := (331 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (153 / 50 : ℝ)) (hi := (157 / 50 : ℝ)) (h := (1773 / 1000 : ℝ)) (e₁ := (303 / 100000 : ℝ)) (e₂ := (297 / 6250 : ℝ)) (c := (9 / 100 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (153 / 25 : ℝ)) (hi := (157 / 25 : ℝ)) (h := (1253 / 500 : ℝ)) (e₁ := (7 / 100000 : ℝ)) (e₂ := (303 / 100000 : ℝ)) (c := (1 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (306 / 25 : ℝ)) (hi := (314 / 25 : ℝ)) (h := (709 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (7 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (612 / 25 : ℝ)) (hi := (628 / 25 : ℝ)) (h := (1253 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_2 {s : ℝ} (ha : (157 / 200 : ℝ) ≤ s) (hb : s ≤ (81 / 100 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (81 / 100 : ℝ)) (h := (9 / 10 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (157 / 200 : ℝ)) (hi := (81 / 100 : ℝ)) (h := (9 / 10 : ℝ)) (e₁ := (2081 / 10000 : ℝ)) (e₂ := (45613 / 100000 : ℝ)) (c := (299 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (157 / 100 : ℝ)) (hi := (81 / 50 : ℝ)) (h := (1273 / 1000 : ℝ)) (e₁ := (1099 / 25000 : ℝ)) (e₂ := (2081 / 10000 : ℝ)) (c := (321 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (157 / 50 : ℝ)) (hi := (81 / 25 : ℝ)) (h := (9 / 5 : ℝ)) (e₁ := (133 / 50000 : ℝ)) (e₂ := (1099 / 25000 : ℝ)) (c := (21 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (157 / 25 : ℝ)) (hi := (162 / 25 : ℝ)) (h := (1273 / 500 : ℝ)) (e₁ := (3 / 50000 : ℝ)) (e₂ := (133 / 50000 : ℝ)) (c := (7 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (314 / 25 : ℝ)) (hi := (324 / 25 : ℝ)) (h := (18 / 5 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (628 / 25 : ℝ)) (hi := (648 / 25 : ℝ)) (h := (1273 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_3 {s : ℝ} (ha : (81 / 100 : ℝ) ≤ s) (hb : s ≤ (337 / 400 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (337 / 400 : ℝ)) (h := (459 / 500 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (81 / 100 : ℝ)) (hi := (337 / 400 : ℝ)) (h := (459 / 500 : ℝ)) (e₁ := (4949 / 25000 : ℝ)) (e₂ := (22243 / 50000 : ℝ)) (c := (591 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (81 / 50 : ℝ)) (hi := (337 / 200 : ℝ)) (h := (1299 / 1000 : ℝ)) (e₁ := (3989 / 100000 : ℝ)) (e₂ := (4949 / 25000 : ℝ)) (c := (309 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (81 / 25 : ℝ)) (hi := (337 / 100 : ℝ)) (h := (459 / 250 : ℝ)) (e₁ := (57 / 25000 : ℝ)) (e₂ := (3989 / 100000 : ℝ)) (c := (39 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (162 / 25 : ℝ)) (hi := (337 / 50 : ℝ)) (h := (2597 / 1000 : ℝ)) (e₁ := (1 / 20000 : ℝ)) (e₂ := (57 / 25000 : ℝ)) (c := (7 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (324 / 25 : ℝ)) (hi := (337 / 25 : ℝ)) (h := (459 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 20000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (648 / 25 : ℝ)) (hi := (674 / 25 : ℝ)) (h := (5193 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_4 {s : ℝ} (ha : (337 / 400 : ℝ) ≤ s) (hb : s ≤ (353 / 400 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (353 / 400 : ℝ)) (h := (47 / 50 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (337 / 400 : ℝ)) (hi := (353 / 400 : ℝ)) (h := (47 / 50 : ℝ)) (e₁ := (2319 / 12500 : ℝ)) (e₂ := (5383 / 12500 : ℝ)) (c := (29 / 50 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (337 / 200 : ℝ)) (hi := (353 / 200 : ℝ)) (h := (1329 / 1000 : ℝ)) (e₁ := (3517 / 100000 : ℝ)) (e₂ := (2319 / 12500 : ℝ)) (c := (147 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (337 / 100 : ℝ)) (hi := (353 / 100 : ℝ)) (h := (1879 / 1000 : ℝ)) (e₁ := (93 / 50000 : ℝ)) (e₂ := (3517 / 100000 : ℝ)) (c := (7 / 100 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (337 / 50 : ℝ)) (hi := (353 / 50 : ℝ)) (h := (1329 / 500 : ℝ)) (e₁ := (1 / 25000 : ℝ)) (e₂ := (93 / 50000 : ℝ)) (c := (3 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (337 / 25 : ℝ)) (hi := (353 / 25 : ℝ)) (h := (1879 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 25000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (674 / 25 : ℝ)) (hi := (706 / 25 : ℝ)) (h := (1063 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_5 {s : ℝ} (ha : (353 / 400 : ℝ) ≤ s) (hb : s ≤ (93 / 100 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (93 / 100 : ℝ)) (h := (193 / 200 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (353 / 400 : ℝ)) (hi := (93 / 100 : ℝ)) (h := (193 / 200 : ℝ)) (e₁ := (2141 / 12500 : ℝ)) (e₂ := (331 / 800 : ℝ)) (c := (113 / 200 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (353 / 200 : ℝ)) (hi := (93 / 50 : ℝ)) (h := (341 / 250 : ℝ)) (e₁ := (603 / 20000 : ℝ)) (e₂ := (2141 / 12500 : ℝ)) (c := (11 / 40 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (353 / 100 : ℝ)) (hi := (93 / 25 : ℝ)) (h := (1929 / 1000 : ℝ)) (e₁ := (73 / 50000 : ℝ)) (e₂ := (603 / 20000 : ℝ)) (c := (61 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (353 / 50 : ℝ)) (hi := (186 / 25 : ℝ)) (h := (341 / 125 : ℝ)) (e₁ := (3 / 100000 : ℝ)) (e₂ := (73 / 50000 : ℝ)) (c := (1 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (353 / 25 : ℝ)) (hi := (372 / 25 : ℝ)) (h := (1929 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (706 / 25 : ℝ)) (hi := (744 / 25 : ℝ)) (h := (682 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_6 {s : ℝ} (ha : (93 / 100 : ℝ) ≤ s) (hb : s ≤ (99 / 100 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (99 / 100 : ℝ)) (h := (199 / 200 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (93 / 100 : ℝ)) (hi := (99 / 100 : ℝ)) (h := (199 / 200 : ℝ)) (e₁ := (15579 / 100000 : ℝ)) (e₂ := (1233 / 3125 : ℝ)) (c := (137 / 250 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (93 / 50 : ℝ)) (hi := (99 / 50 : ℝ)) (h := (176 / 125 : ℝ)) (e₁ := (503 / 20000 : ℝ)) (e₂ := (15579 / 100000 : ℝ)) (c := (51 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (93 / 25 : ℝ)) (hi := (99 / 25 : ℝ)) (h := (199 / 100 : ℝ)) (e₁ := (111 / 100000 : ℝ)) (e₂ := (503 / 20000 : ℝ)) (c := (53 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (186 / 25 : ℝ)) (hi := (198 / 25 : ℝ)) (h := (563 / 200 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (111 / 100000 : ℝ)) (c := (1 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (372 / 25 : ℝ)) (hi := (396 / 25 : ℝ)) (h := (199 / 50 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (744 / 25 : ℝ)) (hi := (792 / 25 : ℝ)) (h := (5629 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_7 {s : ℝ} (ha : (99 / 100 : ℝ) ≤ s) (hb : s ≤ (17 / 16 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (17 / 16 : ℝ)) (h := (1031 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (99 / 100 : ℝ)) (hi := (17 / 16 : ℝ)) (h := (1031 / 1000 : ℝ)) (e₁ := (6911 / 50000 : ℝ)) (e₂ := (37159 / 100000 : ℝ)) (c := (263 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (99 / 50 : ℝ)) (hi := (17 / 8 : ℝ)) (h := (729 / 500 : ℝ)) (e₁ := (401 / 20000 : ℝ)) (e₂ := (6911 / 50000 : ℝ)) (c := (231 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (99 / 25 : ℝ)) (hi := (17 / 4 : ℝ)) (h := (1031 / 500 : ℝ)) (e₁ := (79 / 100000 : ℝ)) (e₂ := (401 / 20000 : ℝ)) (c := (43 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (198 / 25 : ℝ)) (hi := (17 / 2 : ℝ)) (h := (729 / 250 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (79 / 100000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (396 / 25 : ℝ)) (hi := (17 : ℝ)) (h := (1031 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (792 / 25 : ℝ)) (hi := (34 : ℝ)) (h := (5831 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_8 {s : ℝ} (ha : (17 / 16 : ℝ) ≤ s) (hb : s ≤ (457 / 400 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (457 / 400 : ℝ)) (h := (1069 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (17 / 16 : ℝ)) (hi := (457 / 400 : ℝ)) (h := (1069 / 1000 : ℝ)) (e₁ := (11963 / 100000 : ℝ)) (e₂ := (216 / 625 : ℝ)) (c := (249 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (17 / 8 : ℝ)) (hi := (457 / 200 : ℝ)) (h := (189 / 125 : ℝ)) (e₁ := (153 / 10000 : ℝ)) (e₂ := (11963 / 100000 : ℝ)) (c := (41 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (17 / 4 : ℝ)) (hi := (457 / 100 : ℝ)) (h := (1069 / 500 : ℝ)) (e₁ := (53 / 100000 : ℝ)) (e₂ := (153 / 10000 : ℝ)) (c := (17 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (17 / 2 : ℝ)) (hi := (457 / 50 : ℝ)) (h := (378 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (53 / 100000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (17 : ℝ)) (hi := (457 / 25 : ℝ)) (h := (1069 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (34 : ℝ)) (hi := (914 / 25 : ℝ)) (h := (6047 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_9 {s : ℝ} (ha : (457 / 400 : ℝ) ≤ s) (hb : s ≤ (123 / 100 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (123 / 100 : ℝ)) (h := (111 / 100 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (457 / 400 : ℝ)) (hi := (123 / 100 : ℝ)) (h := (111 / 100 : ℝ)) (e₁ := (10203 / 100000 : ℝ)) (e₂ := (31903 / 100000 : ℝ)) (c := (117 / 250 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (457 / 200 : ℝ)) (hi := (123 / 50 : ℝ)) (h := (1569 / 1000 : ℝ)) (e₁ := (571 / 50000 : ℝ)) (e₂ := (10203 / 100000 : ℝ)) (c := (179 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (457 / 100 : ℝ)) (hi := (123 / 25 : ℝ)) (h := (2219 / 1000 : ℝ)) (e₁ := (7 / 20000 : ℝ)) (e₂ := (571 / 50000 : ℝ)) (c := (27 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (457 / 50 : ℝ)) (hi := (246 / 25 : ℝ)) (h := (3137 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (7 / 20000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (457 / 25 : ℝ)) (hi := (492 / 25 : ℝ)) (h := (4437 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (914 / 25 : ℝ)) (hi := (984 / 25 : ℝ)) (h := (3137 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_10 {s : ℝ} (ha : (123 / 100 : ℝ) ≤ s) (hb : s ≤ (529 / 400 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (529 / 400 : ℝ)) (h := (23 / 20 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (123 / 100 : ℝ)) (hi := (529 / 400 : ℝ)) (h := (23 / 20 : ℝ)) (e₁ := (8577 / 100000 : ℝ)) (e₂ := (29231 / 100000 : ℝ)) (c := (87 / 200 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (123 / 50 : ℝ)) (hi := (529 / 200 : ℝ)) (h := (1627 / 1000 : ℝ)) (e₁ := (167 / 20000 : ℝ)) (e₂ := (8577 / 100000 : ℝ)) (c := (77 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (123 / 25 : ℝ)) (hi := (529 / 100 : ℝ)) (h := (23 / 10 : ℝ)) (e₁ := (23 / 100000 : ℝ)) (e₂ := (167 / 20000 : ℝ)) (c := (1 / 50 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (246 / 25 : ℝ)) (hi := (529 / 50 : ℝ)) (h := (3253 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (23 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (492 / 25 : ℝ)) (hi := (529 / 25 : ℝ)) (h := (23 / 5 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (984 / 25 : ℝ)) (hi := (1058 / 25 : ℝ)) (h := (3253 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_11 {s : ℝ} (ha : (529 / 400 : ℝ) ≤ s) (hb : s ≤ (113 / 80 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (113 / 80 : ℝ)) (h := (1189 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (529 / 400 : ℝ)) (hi := (113 / 80 : ℝ)) (h := (1189 / 1000 : ℝ)) (e₁ := (7143 / 100000 : ℝ)) (e₂ := (26649 / 100000 : ℝ)) (c := (201 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (529 / 200 : ℝ)) (hi := (113 / 40 : ℝ)) (h := (1681 / 1000 : ℝ)) (e₁ := (121 / 20000 : ℝ)) (e₂ := (7143 / 100000 : ℝ)) (c := (131 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (529 / 100 : ℝ)) (hi := (113 / 20 : ℝ)) (h := (2377 / 1000 : ℝ)) (e₁ := (3 / 20000 : ℝ)) (e₂ := (121 / 20000 : ℝ)) (c := (3 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (529 / 50 : ℝ)) (hi := (113 / 10 : ℝ)) (h := (1681 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 20000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (529 / 25 : ℝ)) (hi := (113 / 5 : ℝ)) (h := (2377 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1058 / 25 : ℝ)) (hi := (226 / 5 : ℝ)) (h := (1681 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_12 {s : ℝ} (ha : (113 / 80 : ℝ) ≤ s) (hb : s ≤ (149 / 100 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (149 / 100 : ℝ)) (h := (1221 / 1000 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (113 / 80 : ℝ)) (hi := (149 / 100 : ℝ)) (h := (1221 / 1000 : ℝ)) (e₁ := (2991 / 50000 : ℝ)) (e₂ := (24357 / 100000 : ℝ)) (c := (371 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (113 / 40 : ℝ)) (hi := (149 / 50 : ℝ)) (h := (1727 / 1000 : ℝ)) (e₁ := (89 / 20000 : ℝ)) (e₂ := (2991 / 50000 : ℝ)) (c := (111 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (113 / 20 : ℝ)) (hi := (149 / 25 : ℝ)) (h := (1221 / 500 : ℝ)) (e₁ := (1 / 10000 : ℝ)) (e₂ := (89 / 20000 : ℝ)) (c := (3 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (113 / 10 : ℝ)) (hi := (298 / 25 : ℝ)) (h := (3453 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 10000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (113 / 5 : ℝ)) (hi := (596 / 25 : ℝ)) (h := (4883 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (226 / 5 : ℝ)) (hi := (1192 / 25 : ℝ)) (h := (3453 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

theorem sign_piece_13 {s : ℝ} (ha : (149 / 100 : ℝ) ≤ s) (hb : s ≤ (3 / 2 : ℝ)) :
    (1613 / 1000 : ℝ) * Real.sqrt s +
      (UpperDisagreement.capTerm s + UpperDisagreement.capTerm (2 * s) + UpperDisagreement.capTerm (4 * s) +
        UpperDisagreement.capTerm (8 * s) + UpperDisagreement.capTerm (16 * s) + UpperDisagreement.capTerm (32 * s)) + 1 / 1000 ≤ (247 / 100 : ℝ) := by
  have e := scaled_sqrt_le (A := (1613 / 1000 : ℝ)) (s := s) (b := (3 / 2 : ℝ)) (h := (49 / 40 : ℝ)) (by norm_num) hb (by norm_num) (by norm_num)
  have b0 := UpperDisagreement.capTerm_le_band (t := s) (lo := (149 / 100 : ℝ)) (hi := (3 / 2 : ℝ)) (h := (49 / 40 : ℝ)) (e₁ := (5139 / 100000 : ℝ)) (e₂ := (22541 / 100000 : ℝ)) (c := (17 / 50 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := UpperDisagreement.capTerm_le_band (t := 2 * s) (lo := (149 / 50 : ℝ)) (hi := (3 : ℝ)) (h := (1733 / 1000 : ℝ)) (e₁ := (69 / 20000 : ℝ)) (e₂ := (5139 / 100000 : ℝ)) (c := (12 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := UpperDisagreement.capTerm_le_band (t := 4 * s) (lo := (149 / 25 : ℝ)) (hi := (6 : ℝ)) (h := (49 / 20 : ℝ)) (e₁ := (1 / 12500 : ℝ)) (e₂ := (69 / 20000 : ℝ)) (c := (9 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := UpperDisagreement.capTerm_le_band (t := 8 * s) (lo := (298 / 25 : ℝ)) (hi := (12 : ℝ)) (h := (693 / 200 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 12500 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := UpperDisagreement.capTerm_le_band (t := 16 * s) (lo := (596 / 25 : ℝ)) (hi := (24 : ℝ)) (h := (4899 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := UpperDisagreement.capTerm_le_band (t := 32 * s) (lo := (1192 / 25 : ℝ)) (hi := (48 : ℝ)) (h := (6929 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  linarith

/-- The offset sum below and above the split `3/4`: at most `247/100` for every first
grid point `s` in `[3/4, 3/2]`. -/
theorem sign_offset_le (s : ℝ) (h1 : 3 / 4 ≤ s) (h2 : s ≤ 3 / 2) (I : ℕ) :
    (1613 / 1000 : ℝ) * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤ (247 / 100 : ℝ) := by
  refine (sign_offset_reduce s h1 I).trans ?_
  rcases le_or_gt s (153 / 200 : ℝ) with hk | hp
  · exact sign_piece_0 h1 hk
  rcases le_or_gt s (157 / 200 : ℝ) with hk | hp
  · exact sign_piece_1 hp.le hk
  rcases le_or_gt s (81 / 100 : ℝ) with hk | hp
  · exact sign_piece_2 hp.le hk
  rcases le_or_gt s (337 / 400 : ℝ) with hk | hp
  · exact sign_piece_3 hp.le hk
  rcases le_or_gt s (353 / 400 : ℝ) with hk | hp
  · exact sign_piece_4 hp.le hk
  rcases le_or_gt s (93 / 100 : ℝ) with hk | hp
  · exact sign_piece_5 hp.le hk
  rcases le_or_gt s (99 / 100 : ℝ) with hk | hp
  · exact sign_piece_6 hp.le hk
  rcases le_or_gt s (17 / 16 : ℝ) with hk | hp
  · exact sign_piece_7 hp.le hk
  rcases le_or_gt s (457 / 400 : ℝ) with hk | hp
  · exact sign_piece_8 hp.le hk
  rcases le_or_gt s (123 / 100 : ℝ) with hk | hp
  · exact sign_piece_9 hp.le hk
  rcases le_or_gt s (529 / 400 : ℝ) with hk | hp
  · exact sign_piece_10 hp.le hk
  rcases le_or_gt s (113 / 80 : ℝ) with hk | hp
  · exact sign_piece_11 hp.le hk
  rcases le_or_gt s (149 / 100 : ℝ) with hk | hp
  · exact sign_piece_12 hp.le hk
  exact sign_piece_13 hp.le h2

end SignOffset

end ThresholdHC.UpperSign
