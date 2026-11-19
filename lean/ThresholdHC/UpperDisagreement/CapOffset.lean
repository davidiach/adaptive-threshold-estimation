import ThresholdHC.UpperCost.Offset

/-! Offset sums of the cap terms behind the sharper disagreement bound.

Consecutive classifiers at caps `2^l` and `2^(l-1)` disagree only if one of
them errs. Each errs at its cap with probability at most `exp(-2*x)`, with
`x = cap*d^2` (Hoeffding at the cap), so the cap part of the disagreement at
level `l` is at most `exp(-2*x_l) + exp(-x_l)`. Along the dyadic grid of `x_l`,
the levels below `12/25` are bounded by one, which adds a geometric sum, and the
first grid point `s` in `[12/25, 24/25]` and its doublings contribute
`capTerm (2^i*s)`. The offset bound `321/100` splits `[12/25, 24/25]` into
pieces and bounds the first six doubled terms on each piece by monotonicity
and a Taylor lower bound for the exponential. -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- The cap part of the disagreement at scale `t`, times `sqrt t`. -/
def capTerm (t : ℝ) : ℝ := Real.sqrt t * (Real.exp (-2 * t) + Real.exp (-t))

theorem capTerm_nonneg (t : ℝ) : 0 ≤ capTerm t :=
  mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

/-- One band: the scale lies in `[lo, hi]` and `sqrt hi ≤ h`. -/
theorem capTerm_le_band {t lo hi h e₁ e₂ c : ℝ} (hlo : lo ≤ t) (hhi : t ≤ hi) (hlo0 : 0 ≤ lo)
    (hh : 0 ≤ h) (hhh : hi ≤ h ^ 2)
    (he₁ : 1 ≤ e₁ * ∑ i ∈ range 8, (2 * lo) ^ i / (i.factorial : ℝ))
    (he₂ : 1 ≤ e₂ * ∑ i ∈ range 8, lo ^ i / (i.factorial : ℝ)) (hc : h * (e₁ + e₂) ≤ c) :
    capTerm t ≤ c := by
  have hst : Real.sqrt t ≤ h := by
    rw [Real.sqrt_le_left hh]
    linarith
  have h1 : Real.exp (-2 * t) ≤ e₁ := by
    have h := exp_neg_le_of_taylor (v := 2 * lo) (c := e₁) (by positivity) 8 he₁
    exact (Real.exp_le_exp.2 (by linarith)).trans h
  have h2 : Real.exp (-t) ≤ e₂ := by
    have h := exp_neg_le_of_taylor (v := lo) (c := e₂) hlo0 8 he₂
    exact (Real.exp_le_exp.2 (by linarith)).trans h
  unfold capTerm
  calc
    _ ≤ h * (e₁ + e₂) :=
      mul_le_mul hst (add_le_add h1 h2) (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hh
    _ ≤ c := hc

/-- Far past the split the cap terms are negligible. -/
theorem capTerm_tail {t : ℝ} (ht : 30 ≤ t) : capTerm t ≤ 1 / (1000 * t) := by
  have ht0 : 0 < t := by linarith
  have hst : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left ht0.le]
    nlinarith
  have hE := Real.pow_div_factorial_le_exp t ht0.le 8
  have he : Real.exp (-t) ≤ 40320 / t ^ 8 := by
    rw [Real.exp_neg]
    have h8 : (0 : ℝ) < t ^ 8 := by positivity
    rw [inv_le_comm₀ (Real.exp_pos t) (by positivity)]
    norm_num [Nat.factorial] at hE
    rw [inv_div]
    linarith
  have he2 : Real.exp (-2 * t) ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
  have h6 : (729000000 : ℝ) ≤ t ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 30) ht 6
    norm_num at this
    linarith
  unfold capTerm
  calc
    _ ≤ t * (2 * (40320 / t ^ 8)) :=
      mul_le_mul hst (by linarith) (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) ht0.le
    _ = 80640 / (t ^ 6 * t) := by field_simp; ring
    _ ≤ 1 / (1000 * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- Keep the first six doubled terms; the rest add at most `1/1000`. -/
theorem cap_offset_reduce (s : ℝ) (h1 : 12 / 25 ≤ s) (I : ℕ) :
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ range I, capTerm (2 ^ i * s) ≤
      (1 + Real.sqrt 2) * Real.sqrt s +
        (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
          capTerm (32 * s)) + 1 / 1000 := by
  have hnn : ∀ i : ℕ, 0 ≤ capTerm (2 ^ i * s) := fun i => capTerm_nonneg _
  have hsplit : ∑ i ∈ range I, capTerm (2 ^ i * s) ≤
      ∑ i ∈ range 6, capTerm (2 ^ i * s) + ∑ i ∈ range I, capTerm (2 ^ (6 + i) * s) := by
    rw [← Finset.sum_range_add]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ => hnn i)
  have htail : ∑ i ∈ range I, capTerm (2 ^ (6 + i) * s) ≤ 1 / 1000 := by
    calc
      _ ≤ ∑ i ∈ range I, (1 / 2000) * (1 / 2 : ℝ) ^ i := by
        apply sum_le_sum
        intro i _
        have hp : (64 : ℝ) * 2 ^ i = 2 ^ (6 + i) := by rw [pow_add]; norm_num
        have hpi : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        have h30 : 30 ≤ 2 ^ (6 + i) * s := by rw [← hp]; nlinarith
        refine (capTerm_tail h30).trans ?_
        rw [one_div_pow, ← hp]
        rw [div_mul_div_comm, one_mul]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      _ = (1 / 2000) * ∑ i ∈ range I, (1 / 2 : ℝ) ^ i := by rw [mul_sum]
      _ ≤ (1 / 2000) * 2 := by gcongr; exact sum_geometric_two_le I
      _ = 1 / 1000 := by norm_num
  have h6 : ∑ i ∈ range 6, capTerm (2 ^ i * s) =
      capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [h6] at hsplit
  linarith

theorem cap_piece_0 {s : ℝ} (ha : (12 / 25 : ℝ) ≤ s) (hb : s ≤ (49 / 100 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (49 / 100 : ℝ)) (h := (7 / 10 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (12 / 25 : ℝ)) (hi := (49 / 100 : ℝ)) (h := (7 / 10 : ℝ)) (e₁ := (3829 / 10000 : ℝ)) (e₂ := (61879 / 100000 : ℝ)) (c := (351 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (24 / 25 : ℝ)) (hi := (49 / 50 : ℝ)) (h := (99 / 100 : ℝ)) (e₁ := (7337 / 50000 : ℝ)) (e₂ := (3829 / 10000 : ℝ)) (c := (21 / 40 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (48 / 25 : ℝ)) (hi := (49 / 25 : ℝ)) (h := (7 / 5 : ℝ)) (e₁ := (561 / 25000 : ℝ)) (e₂ := (7337 / 50000 : ℝ)) (c := (237 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (96 / 25 : ℝ)) (hi := (98 / 25 : ℝ)) (h := (99 / 50 : ℝ)) (e₁ := (93 / 100000 : ℝ)) (e₂ := (561 / 25000 : ℝ)) (c := (47 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (192 / 25 : ℝ)) (hi := (196 / 25 : ℝ)) (h := (14 / 5 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (93 / 100000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (384 / 25 : ℝ)) (hi := (392 / 25 : ℝ)) (h := (99 / 25 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_1 {s : ℝ} (ha : (49 / 100 : ℝ) ≤ s) (hb : s ≤ (201 / 400 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (201 / 400 : ℝ)) (h := (709 / 1000 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (49 / 100 : ℝ)) (hi := (201 / 400 : ℝ)) (h := (709 / 1000 : ℝ)) (e₁ := (9383 / 25000 : ℝ)) (e₂ := (61263 / 100000 : ℝ)) (c := (701 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (49 / 50 : ℝ)) (hi := (201 / 200 : ℝ)) (h := (1003 / 1000 : ℝ)) (e₁ := (141 / 1000 : ℝ)) (e₂ := (9383 / 25000 : ℝ)) (c := (259 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (49 / 25 : ℝ)) (hi := (201 / 100 : ℝ)) (h := (709 / 500 : ℝ)) (e₁ := (2081 / 100000 : ℝ)) (e₂ := (141 / 1000 : ℝ)) (c := (23 / 100 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (98 / 25 : ℝ)) (hi := (201 / 50 : ℝ)) (h := (401 / 200 : ℝ)) (e₁ := (83 / 100000 : ℝ)) (e₂ := (2081 / 100000 : ℝ)) (c := (11 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (196 / 25 : ℝ)) (hi := (201 / 25 : ℝ)) (h := (709 / 250 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (83 / 100000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (392 / 25 : ℝ)) (hi := (402 / 25 : ℝ)) (h := (401 / 100 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_2 {s : ℝ} (ha : (201 / 400 : ℝ) ≤ s) (hb : s ≤ (103 / 200 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (103 / 200 : ℝ)) (h := (359 / 500 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (201 / 400 : ℝ)) (hi := (103 / 200 : ℝ)) (h := (359 / 500 : ℝ)) (e₁ := (7321 / 20000 : ℝ)) (e₂ := (30251 / 50000 : ℝ)) (c := (349 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (201 / 200 : ℝ)) (hi := (103 / 100 : ℝ)) (h := (203 / 200 : ℝ)) (e₁ := (2683 / 20000 : ℝ)) (e₂ := (7321 / 20000 : ℝ)) (c := (127 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (201 / 100 : ℝ)) (hi := (103 / 50 : ℝ)) (h := (359 / 250 : ℝ)) (e₁ := (379 / 20000 : ℝ)) (e₂ := (2683 / 20000 : ℝ)) (c := (11 / 50 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (201 / 50 : ℝ)) (hi := (103 / 25 : ℝ)) (h := (203 / 100 : ℝ)) (e₁ := (73 / 100000 : ℝ)) (e₂ := (379 / 20000 : ℝ)) (c := (1 / 25 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (201 / 25 : ℝ)) (hi := (206 / 25 : ℝ)) (h := (2871 / 1000 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (73 / 100000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (402 / 25 : ℝ)) (hi := (412 / 25 : ℝ)) (h := (203 / 50 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_3 {s : ℝ} (ha : (103 / 200 : ℝ) ≤ s) (hb : s ≤ (53 / 100 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (53 / 100 : ℝ)) (h := (729 / 1000 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (103 / 200 : ℝ)) (hi := (53 / 100 : ℝ)) (h := (729 / 1000 : ℝ)) (e₁ := (17851 / 50000 : ℝ)) (e₂ := (59751 / 100000 : ℝ)) (c := (87 / 125 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (103 / 100 : ℝ)) (hi := (53 / 50 : ℝ)) (h := (103 / 100 : ℝ)) (e₁ := (12763 / 100000 : ℝ)) (e₂ := (17851 / 50000 : ℝ)) (c := (1 / 2 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (103 / 50 : ℝ)) (hi := (53 / 25 : ℝ)) (h := (1457 / 1000 : ℝ)) (e₁ := (863 / 50000 : ℝ)) (e₂ := (12763 / 100000 : ℝ)) (c := (53 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (103 / 25 : ℝ)) (hi := (106 / 25 : ℝ)) (h := (103 / 50 : ℝ)) (e₁ := (63 / 100000 : ℝ)) (e₂ := (863 / 50000 : ℝ)) (c := (37 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (206 / 25 : ℝ)) (hi := (212 / 25 : ℝ)) (h := (2913 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (63 / 100000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (412 / 25 : ℝ)) (hi := (424 / 25 : ℝ)) (h := (4119 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_4 {s : ℝ} (ha : (53 / 100 : ℝ) ≤ s) (hb : s ≤ (219 / 400 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (219 / 400 : ℝ)) (h := (37 / 50 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (53 / 100 : ℝ)) (hi := (219 / 400 : ℝ)) (h := (37 / 50 : ℝ)) (e₁ := (34647 / 100000 : ℝ)) (e₂ := (58861 / 100000 : ℝ)) (c := (173 / 250 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (53 / 50 : ℝ)) (hi := (219 / 200 : ℝ)) (h := (1047 / 1000 : ℝ)) (e₁ := (12023 / 100000 : ℝ)) (e₂ := (34647 / 100000 : ℝ)) (c := (489 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (53 / 25 : ℝ)) (hi := (219 / 100 : ℝ)) (h := (37 / 25 : ℝ)) (e₁ := (193 / 12500 : ℝ)) (e₂ := (12023 / 100000 : ℝ)) (c := (201 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (106 / 25 : ℝ)) (hi := (219 / 50 : ℝ)) (h := (2093 / 1000 : ℝ)) (e₁ := (27 / 50000 : ℝ)) (e₂ := (193 / 12500 : ℝ)) (c := (17 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (212 / 25 : ℝ)) (hi := (219 / 25 : ℝ)) (h := (74 / 25 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (27 / 50000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (424 / 25 : ℝ)) (hi := (438 / 25 : ℝ)) (h := (2093 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_5 {s : ℝ} (ha : (219 / 400 : ℝ) ≤ s) (hb : s ≤ (113 / 200 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (113 / 200 : ℝ)) (h := (94 / 125 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (219 / 400 : ℝ)) (hi := (113 / 200 : ℝ)) (h := (94 / 125 : ℝ)) (e₁ := (6691 / 20000 : ℝ)) (e₂ := (723 / 1250 : ℝ)) (c := (687 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (219 / 200 : ℝ)) (hi := (113 / 100 : ℝ)) (h := (133 / 125 : ℝ)) (e₁ := (5607 / 50000 : ℝ)) (e₂ := (6691 / 20000 : ℝ)) (c := (119 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (219 / 100 : ℝ)) (hi := (113 / 50 : ℝ)) (h := (188 / 125 : ℝ)) (e₁ := (679 / 50000 : ℝ)) (e₂ := (5607 / 50000 : ℝ)) (c := (19 / 100 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (219 / 50 : ℝ)) (hi := (113 / 25 : ℝ)) (h := (2127 / 1000 : ℝ)) (e₁ := (9 / 20000 : ℝ)) (e₂ := (679 / 50000 : ℝ)) (c := (3 / 100 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (219 / 25 : ℝ)) (hi := (226 / 25 : ℝ)) (h := (3007 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (9 / 20000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (438 / 25 : ℝ)) (hi := (452 / 25 : ℝ)) (h := (4253 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_6 {s : ℝ} (ha : (113 / 200 : ℝ) ≤ s) (hb : s ≤ (47 / 80 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (47 / 80 : ℝ)) (h := (767 / 1000 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (113 / 200 : ℝ)) (hi := (47 / 80 : ℝ)) (h := (767 / 1000 : ℝ)) (e₁ := (6461 / 20000 : ℝ)) (e₂ := (56837 / 100000 : ℝ)) (c := (171 / 250 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (113 / 100 : ℝ)) (hi := (47 / 40 : ℝ)) (h := (271 / 250 : ℝ)) (e₁ := (523 / 5000 : ℝ)) (e₂ := (6461 / 20000 : ℝ)) (c := (58 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (113 / 50 : ℝ)) (hi := (47 / 20 : ℝ)) (h := (1533 / 1000 : ℝ)) (e₁ := (239 / 20000 : ℝ)) (e₂ := (523 / 5000 : ℝ)) (c := (179 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (113 / 25 : ℝ)) (hi := (47 / 10 : ℝ)) (h := (271 / 125 : ℝ)) (e₁ := (19 / 50000 : ℝ)) (e₂ := (239 / 20000 : ℝ)) (c := (27 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (226 / 25 : ℝ)) (hi := (47 / 5 : ℝ)) (h := (1533 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (19 / 50000 : ℝ)) (c := (1 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (452 / 25 : ℝ)) (hi := (94 / 5 : ℝ)) (h := (542 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_7 {s : ℝ} (ha : (47 / 80 : ℝ) ≤ s) (hb : s ≤ (49 / 80 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (49 / 80 : ℝ)) (h := (783 / 1000 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (47 / 80 : ℝ)) (hi := (49 / 80 : ℝ)) (h := (783 / 1000 : ℝ)) (e₁ := (30883 / 100000 : ℝ)) (e₂ := (13893 / 25000 : ℝ)) (c := (677 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (47 / 40 : ℝ)) (hi := (49 / 40 : ℝ)) (h := (1107 / 1000 : ℝ)) (e₁ := (4783 / 50000 : ℝ)) (e₂ := (30883 / 100000 : ℝ)) (c := (56 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (47 / 20 : ℝ)) (hi := (49 / 20 : ℝ)) (h := (783 / 500 : ℝ)) (e₁ := (127 / 12500 : ℝ)) (e₂ := (4783 / 50000 : ℝ)) (c := (83 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (47 / 10 : ℝ)) (hi := (49 / 10 : ℝ)) (h := (1107 / 500 : ℝ)) (e₁ := (3 / 10000 : ℝ)) (e₂ := (127 / 12500 : ℝ)) (c := (3 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (47 / 5 : ℝ)) (hi := (49 / 5 : ℝ)) (h := (3131 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 10000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (94 / 5 : ℝ)) (hi := (98 / 5 : ℝ)) (h := (1107 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_8 {s : ℝ} (ha : (49 / 80 : ℝ) ≤ s) (hb : s ≤ (16 / 25 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (16 / 25 : ℝ)) (h := (4 / 5 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (49 / 80 : ℝ)) (hi := (16 / 25 : ℝ)) (h := (4 / 5 : ℝ)) (e₁ := (14689 / 50000 : ℝ)) (e₂ := (271 / 500 : ℝ)) (c := (669 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (49 / 40 : ℝ)) (hi := (32 / 25 : ℝ)) (h := (283 / 250 : ℝ)) (e₁ := (8663 / 100000 : ℝ)) (e₂ := (14689 / 50000 : ℝ)) (c := (431 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (49 / 20 : ℝ)) (hi := (64 / 25 : ℝ)) (h := (8 / 5 : ℝ)) (e₁ := (17 / 2000 : ℝ)) (e₂ := (8663 / 100000 : ℝ)) (c := (153 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (49 / 10 : ℝ)) (hi := (128 / 25 : ℝ)) (h := (2263 / 1000 : ℝ)) (e₁ := (3 / 12500 : ℝ)) (e₂ := (17 / 2000 : ℝ)) (c := (1 / 50 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (49 / 5 : ℝ)) (hi := (256 / 25 : ℝ)) (h := (16 / 5 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 12500 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (98 / 5 : ℝ)) (hi := (512 / 25 : ℝ)) (h := (2263 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_9 {s : ℝ} (ha : (16 / 25 : ℝ) ≤ s) (hb : s ≤ (67 / 100 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (67 / 100 : ℝ)) (h := (819 / 1000 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (16 / 25 : ℝ)) (hi := (67 / 100 : ℝ)) (h := (819 / 1000 : ℝ)) (e₁ := (13903 / 50000 : ℝ)) (e₂ := (5273 / 10000 : ℝ)) (c := (33 / 50 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (32 / 25 : ℝ)) (hi := (67 / 50 : ℝ)) (h := (579 / 500 : ℝ)) (e₁ := (7769 / 100000 : ℝ)) (e₂ := (13903 / 50000 : ℝ)) (c := (103 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (64 / 25 : ℝ)) (hi := (67 / 25 : ℝ)) (h := (819 / 500 : ℝ)) (e₁ := (7 / 1000 : ℝ)) (e₂ := (7769 / 100000 : ℝ)) (c := (139 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (128 / 25 : ℝ)) (hi := (134 / 25 : ℝ)) (h := (579 / 250 : ℝ)) (e₁ := (9 / 50000 : ℝ)) (e₂ := (7 / 1000 : ℝ)) (c := (17 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (256 / 25 : ℝ)) (hi := (268 / 25 : ℝ)) (h := (131 / 40 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (9 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (512 / 25 : ℝ)) (hi := (536 / 25 : ℝ)) (h := (4631 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_10 {s : ℝ} (ha : (67 / 100 : ℝ) ≤ s) (hb : s ≤ (7 / 10 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (7 / 10 : ℝ)) (h := (837 / 1000 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (67 / 100 : ℝ)) (hi := (7 / 10 : ℝ)) (h := (837 / 1000 : ℝ)) (e₁ := (26187 / 100000 : ℝ)) (e₂ := (51171 / 100000 : ℝ)) (c := (81 / 125 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (67 / 50 : ℝ)) (hi := (7 / 5 : ℝ)) (h := (148 / 125 : ℝ)) (e₁ := (6901 / 100000 : ℝ)) (e₂ := (26187 / 100000 : ℝ)) (c := (49 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (67 / 25 : ℝ)) (hi := (14 / 5 : ℝ)) (h := (837 / 500 : ℝ)) (e₁ := (569 / 100000 : ℝ)) (e₂ := (6901 / 100000 : ℝ)) (c := (63 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (134 / 25 : ℝ)) (hi := (28 / 5 : ℝ)) (h := (2367 / 1000 : ℝ)) (e₁ := (7 / 50000 : ℝ)) (e₂ := (569 / 100000 : ℝ)) (c := (7 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (268 / 25 : ℝ)) (hi := (56 / 5 : ℝ)) (h := (3347 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (7 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (536 / 25 : ℝ)) (hi := (112 / 5 : ℝ)) (h := (4733 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_11 {s : ℝ} (ha : (7 / 10 : ℝ) ≤ s) (hb : s ≤ (293 / 400 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (293 / 400 : ℝ)) (h := (107 / 125 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (7 / 10 : ℝ)) (hi := (293 / 400 : ℝ)) (h := (107 / 125 : ℝ)) (e₁ := (24663 / 100000 : ℝ)) (e₂ := (49659 / 100000 : ℝ)) (c := (637 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (7 / 5 : ℝ)) (hi := (293 / 200 : ℝ)) (h := (1211 / 1000 : ℝ)) (e₁ := (6131 / 100000 : ℝ)) (e₂ := (24663 / 100000 : ℝ)) (c := (373 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (14 / 5 : ℝ)) (hi := (293 / 100 : ℝ)) (h := (214 / 125 : ℝ)) (e₁ := (29 / 6250 : ℝ)) (e₂ := (6131 / 100000 : ℝ)) (c := (113 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (28 / 5 : ℝ)) (hi := (293 / 50 : ℝ)) (h := (2421 / 1000 : ℝ)) (e₁ := (11 / 100000 : ℝ)) (e₂ := (29 / 6250 : ℝ)) (c := (3 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (56 / 5 : ℝ)) (hi := (293 / 25 : ℝ)) (h := (428 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (11 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (112 / 5 : ℝ)) (hi := (586 / 25 : ℝ)) (h := (2421 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_12 {s : ℝ} (ha : (293 / 400 : ℝ) ≤ s) (hb : s ≤ (153 / 200 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (153 / 200 : ℝ)) (h := (7 / 8 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (293 / 400 : ℝ)) (hi := (153 / 200 : ℝ)) (h := (7 / 8 : ℝ)) (e₁ := (2889 / 12500 : ℝ)) (e₂ := (48071 / 100000 : ℝ)) (c := (623 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (293 / 200 : ℝ)) (hi := (153 / 100 : ℝ)) (h := (1237 / 1000 : ℝ)) (e₁ := (5397 / 100000 : ℝ)) (e₂ := (2889 / 12500 : ℝ)) (c := (353 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (293 / 100 : ℝ)) (hi := (153 / 50 : ℝ)) (h := (7 / 4 : ℝ)) (e₁ := (187 / 50000 : ℝ)) (e₂ := (5397 / 100000 : ℝ)) (c := (101 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (293 / 50 : ℝ)) (hi := (153 / 25 : ℝ)) (h := (1237 / 500 : ℝ)) (e₁ := (1 / 12500 : ℝ)) (e₂ := (187 / 50000 : ℝ)) (c := (1 / 100 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (293 / 25 : ℝ)) (hi := (306 / 25 : ℝ)) (h := (3499 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 12500 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (586 / 25 : ℝ)) (hi := (612 / 25 : ℝ)) (h := (1237 / 250 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_13 {s : ℝ} (ha : (153 / 200 : ℝ) ≤ s) (hb : s ≤ (4 / 5 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (4 / 5 : ℝ)) (h := (179 / 200 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (153 / 200 : ℝ)) (hi := (4 / 5 : ℝ)) (h := (179 / 200 : ℝ)) (e₁ := (10829 / 50000 : ℝ)) (e₂ := (23267 / 50000 : ℝ)) (c := (611 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (153 / 100 : ℝ)) (hi := (8 / 5 : ℝ)) (h := (253 / 200 : ℝ)) (e₁ := (297 / 6250 : ℝ)) (e₂ := (10829 / 50000 : ℝ)) (c := (67 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (153 / 50 : ℝ)) (hi := (16 / 5 : ℝ)) (h := (1789 / 1000 : ℝ)) (e₁ := (303 / 100000 : ℝ)) (e₂ := (297 / 6250 : ℝ)) (c := (91 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (153 / 25 : ℝ)) (hi := (32 / 5 : ℝ)) (h := (253 / 100 : ℝ)) (e₁ := (7 / 100000 : ℝ)) (e₂ := (303 / 100000 : ℝ)) (c := (1 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (306 / 25 : ℝ)) (hi := (64 / 5 : ℝ)) (h := (1789 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (7 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (612 / 25 : ℝ)) (hi := (128 / 5 : ℝ)) (h := (253 / 50 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_14 {s : ℝ} (ha : (4 / 5 : ℝ) ≤ s) (hb : s ≤ (167 / 200 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (167 / 200 : ℝ)) (h := (457 / 500 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (4 / 5 : ℝ)) (hi := (167 / 200 : ℝ)) (h := (457 / 500 : ℝ)) (e₁ := (4039 / 20000 : ℝ)) (e₂ := (44933 / 100000 : ℝ)) (c := (149 / 250 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (8 / 5 : ℝ)) (hi := (167 / 100 : ℝ)) (h := (1293 / 1000 : ℝ)) (e₁ := (2073 / 50000 : ℝ)) (e₂ := (4039 / 20000 : ℝ)) (c := (63 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (16 / 5 : ℝ)) (hi := (167 / 50 : ℝ)) (h := (457 / 250 : ℝ)) (e₁ := (121 / 50000 : ℝ)) (e₂ := (2073 / 50000 : ℝ)) (c := (81 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (32 / 5 : ℝ)) (hi := (167 / 25 : ℝ)) (h := (517 / 200 : ℝ)) (e₁ := (1 / 20000 : ℝ)) (e₂ := (121 / 50000 : ℝ)) (c := (7 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (64 / 5 : ℝ)) (hi := (334 / 25 : ℝ)) (h := (457 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 20000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (128 / 5 : ℝ)) (hi := (668 / 25 : ℝ)) (h := (517 / 100 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_15 {s : ℝ} (ha : (167 / 200 : ℝ) ≤ s) (hb : s ≤ (347 / 400 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (347 / 400 : ℝ)) (h := (233 / 250 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (167 / 200 : ℝ)) (hi := (347 / 400 : ℝ)) (h := (233 / 250 : ℝ)) (e₁ := (1177 / 6250 : ℝ)) (e₂ := (10847 / 25000 : ℝ)) (c := (29 / 50 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (167 / 100 : ℝ)) (hi := (347 / 200 : ℝ)) (h := (659 / 500 : ℝ)) (e₁ := (181 / 5000 : ℝ)) (e₂ := (1177 / 6250 : ℝ)) (c := (37 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (167 / 50 : ℝ)) (hi := (347 / 100 : ℝ)) (h := (1863 / 1000 : ℝ)) (e₁ := (39 / 20000 : ℝ)) (e₂ := (181 / 5000 : ℝ)) (c := (9 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (167 / 25 : ℝ)) (hi := (347 / 50 : ℝ)) (h := (527 / 200 : ℝ)) (e₁ := (1 / 25000 : ℝ)) (e₂ := (39 / 20000 : ℝ)) (c := (3 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (334 / 25 : ℝ)) (hi := (347 / 25 : ℝ)) (h := (1863 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 25000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (668 / 25 : ℝ)) (hi := (694 / 25 : ℝ)) (h := (5269 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_16 {s : ℝ} (ha : (347 / 400 : ℝ) ≤ s) (hb : s ≤ (359 / 400 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (359 / 400 : ℝ)) (h := (237 / 250 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (347 / 400 : ℝ)) (hi := (359 / 400 : ℝ)) (h := (237 / 250 : ℝ)) (e₁ := (1103 / 6250 : ℝ)) (e₂ := (42001 / 100000 : ℝ)) (c := (283 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (347 / 200 : ℝ)) (hi := (359 / 200 : ℝ)) (h := (67 / 50 : ℝ)) (e₁ := (1597 / 50000 : ℝ)) (e₂ := (1103 / 6250 : ℝ)) (c := (7 / 25 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (347 / 100 : ℝ)) (hi := (359 / 100 : ℝ)) (h := (379 / 200 : ℝ)) (e₁ := (1 / 625 : ℝ)) (e₂ := (1597 / 50000 : ℝ)) (c := (8 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (347 / 50 : ℝ)) (hi := (359 / 50 : ℝ)) (h := (67 / 25 : ℝ)) (e₁ := (3 / 100000 : ℝ)) (e₂ := (1 / 625 : ℝ)) (c := (1 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (347 / 25 : ℝ)) (hi := (359 / 25 : ℝ)) (h := (379 / 100 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (694 / 25 : ℝ)) (hi := (718 / 25 : ℝ)) (h := (134 / 25 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_17 {s : ℝ} (ha : (359 / 400 : ℝ) ≤ s) (hb : s ≤ (37 / 40 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (37 / 40 : ℝ)) (h := (481 / 500 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (359 / 400 : ℝ)) (hi := (37 / 40 : ℝ)) (h := (481 / 500 : ℝ)) (e₁ := (8311 / 50000 : ℝ)) (e₂ := (40759 / 100000 : ℝ)) (c := (553 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (359 / 200 : ℝ)) (hi := (37 / 20 : ℝ)) (h := (1361 / 1000 : ℝ)) (e₁ := (2847 / 100000 : ℝ)) (e₂ := (8311 / 50000 : ℝ)) (c := (53 / 200 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (359 / 100 : ℝ)) (hi := (37 / 10 : ℝ)) (h := (481 / 250 : ℝ)) (e₁ := (67 / 50000 : ℝ)) (e₂ := (2847 / 100000 : ℝ)) (c := (29 / 500 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (359 / 50 : ℝ)) (hi := (37 / 5 : ℝ)) (h := (2721 / 1000 : ℝ)) (e₁ := (3 / 100000 : ℝ)) (e₂ := (67 / 50000 : ℝ)) (c := (1 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (359 / 25 : ℝ)) (hi := (74 / 5 : ℝ)) (h := (481 / 125 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (3 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (718 / 25 : ℝ)) (hi := (148 / 5 : ℝ)) (h := (5441 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_18 {s : ℝ} (ha : (37 / 40 : ℝ) ≤ s) (hb : s ≤ (19 / 20 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (19 / 20 : ℝ)) (h := (39 / 40 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (37 / 40 : ℝ)) (hi := (19 / 20 : ℝ)) (h := (39 / 40 : ℝ)) (e₁ := (3147 / 20000 : ℝ)) (e₂ := (19827 / 50000 : ℝ)) (c := (541 / 1000 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (37 / 20 : ℝ)) (hi := (19 / 10 : ℝ)) (h := (1379 / 1000 : ℝ)) (e₁ := (2563 / 100000 : ℝ)) (e₂ := (3147 / 20000 : ℝ)) (c := (253 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (37 / 10 : ℝ)) (hi := (19 / 5 : ℝ)) (h := (39 / 20 : ℝ)) (e₁ := (57 / 50000 : ℝ)) (e₂ := (2563 / 100000 : ℝ)) (c := (53 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (37 / 5 : ℝ)) (hi := (38 / 5 : ℝ)) (h := (2757 / 1000 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (57 / 50000 : ℝ)) (c := (1 / 250 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (74 / 5 : ℝ)) (hi := (76 / 5 : ℝ)) (h := (3899 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (148 / 5 : ℝ)) (hi := (152 / 5 : ℝ)) (h := (2757 / 500 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

theorem cap_piece_19 {s : ℝ} (ha : (19 / 20 : ℝ) ≤ s) (hb : s ≤ (24 / 25 : ℝ)) :
    (1 + Real.sqrt 2) * Real.sqrt s +
      (capTerm s + capTerm (2 * s) + capTerm (4 * s) + capTerm (8 * s) + capTerm (16 * s) +
        capTerm (32 * s)) + 1 / 1000 ≤ (321 / 100 : ℝ) := by
  have e := UpperCost.base_le (s := s) (b := (24 / 25 : ℝ)) (h := (49 / 50 : ℝ)) hb (by norm_num) (by norm_num)
  have b0 := capTerm_le_band (t := s) (lo := (19 / 20 : ℝ)) (hi := (24 / 25 : ℝ)) (h := (49 / 50 : ℝ)) (e₁ := (14969 / 100000 : ℝ)) (e₂ := (1547 / 4000 : ℝ)) (c := (263 / 500 : ℝ))
    ha hb (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b1 := capTerm_le_band (t := 2 * s) (lo := (19 / 10 : ℝ)) (hi := (48 / 25 : ℝ)) (h := (693 / 500 : ℝ)) (e₁ := (2331 / 100000 : ℝ)) (e₂ := (14969 / 100000 : ℝ)) (c := (6 / 25 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b2 := capTerm_le_band (t := 4 * s) (lo := (19 / 5 : ℝ)) (hi := (96 / 25 : ℝ)) (h := (49 / 25 : ℝ)) (e₁ := (99 / 100000 : ℝ)) (e₂ := (2331 / 100000 : ℝ)) (c := (6 / 125 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b3 := capTerm_le_band (t := 8 * s) (lo := (38 / 5 : ℝ)) (hi := (192 / 25 : ℝ)) (h := (693 / 250 : ℝ)) (e₁ := (1 / 50000 : ℝ)) (e₂ := (99 / 100000 : ℝ)) (c := (3 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b4 := capTerm_le_band (t := 16 * s) (lo := (76 / 5 : ℝ)) (hi := (384 / 25 : ℝ)) (h := (98 / 25 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 50000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  have b5 := capTerm_le_band (t := 32 * s) (lo := (152 / 5 : ℝ)) (hi := (768 / 25 : ℝ)) (h := (5543 / 1000 : ℝ)) (e₁ := (1 / 100000 : ℝ)) (e₂ := (1 / 100000 : ℝ)) (c := (1 / 1000 : ℝ))
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num)
  norm_num at e
  linarith

/-- The offset sum of the cap terms: at most `321/100` for every first grid point `s`
in `[12/25, 24/25]`. -/
theorem cap_offset_le (s : ℝ) (h1 : 12 / 25 ≤ s) (h2 : s ≤ 24 / 25) (I : ℕ) :
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ range I, capTerm (2 ^ i * s) ≤ (321 / 100 : ℝ) := by
  refine (cap_offset_reduce s h1 I).trans ?_
  rcases le_or_gt s (49 / 100 : ℝ) with hk | hp
  · exact cap_piece_0 h1 hk
  rcases le_or_gt s (201 / 400 : ℝ) with hk | hp
  · exact cap_piece_1 hp.le hk
  rcases le_or_gt s (103 / 200 : ℝ) with hk | hp
  · exact cap_piece_2 hp.le hk
  rcases le_or_gt s (53 / 100 : ℝ) with hk | hp
  · exact cap_piece_3 hp.le hk
  rcases le_or_gt s (219 / 400 : ℝ) with hk | hp
  · exact cap_piece_4 hp.le hk
  rcases le_or_gt s (113 / 200 : ℝ) with hk | hp
  · exact cap_piece_5 hp.le hk
  rcases le_or_gt s (47 / 80 : ℝ) with hk | hp
  · exact cap_piece_6 hp.le hk
  rcases le_or_gt s (49 / 80 : ℝ) with hk | hp
  · exact cap_piece_7 hp.le hk
  rcases le_or_gt s (16 / 25 : ℝ) with hk | hp
  · exact cap_piece_8 hp.le hk
  rcases le_or_gt s (67 / 100 : ℝ) with hk | hp
  · exact cap_piece_9 hp.le hk
  rcases le_or_gt s (7 / 10 : ℝ) with hk | hp
  · exact cap_piece_10 hp.le hk
  rcases le_or_gt s (293 / 400 : ℝ) with hk | hp
  · exact cap_piece_11 hp.le hk
  rcases le_or_gt s (153 / 200 : ℝ) with hk | hp
  · exact cap_piece_12 hp.le hk
  rcases le_or_gt s (4 / 5 : ℝ) with hk | hp
  · exact cap_piece_13 hp.le hk
  rcases le_or_gt s (167 / 200 : ℝ) with hk | hp
  · exact cap_piece_14 hp.le hk
  rcases le_or_gt s (347 / 400 : ℝ) with hk | hp
  · exact cap_piece_15 hp.le hk
  rcases le_or_gt s (359 / 400 : ℝ) with hk | hp
  · exact cap_piece_16 hp.le hk
  rcases le_or_gt s (37 / 40 : ℝ) with hk | hp
  · exact cap_piece_17 hp.le hk
  rcases le_or_gt s (19 / 20 : ℝ) with hk | hp
  · exact cap_piece_18 hp.le hk
  exact cap_piece_19 hp.le h2

end ThresholdHC.UpperDisagreement
