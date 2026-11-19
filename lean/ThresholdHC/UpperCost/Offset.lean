import ThresholdHC.UpperWork.Dyadic

/-! Offset sums behind the sharper call-cost bound.

At the check with `n` flips, the cap-`2^l` classifier survives with probability at
most `exp(-2*n*(d-t)^2)` once its threshold `t` is below the gap `d`. In the
call-cost sum, the levels `l` and checks `k` with a fixed difference
`j = l - k` share the threshold scale `v = 1 + j*log 2`: the threshold is below
`d` exactly when `cap k*d^2 ≥ v`. Along the dyadic grid of `cap k*d^2/v`, the
checks below the scale contribute a geometric sum, and the first grid point
`s` in `[1, 2]` and its doublings contribute `tailTerm v (2^i*s)` in units of
`sqrt v`. The two offset bounds here cover `v ≥ 169/100` and `v ≥ 119/50`. Each
splits `[1, 2]` into pieces and bounds the first four doubled terms on each
piece by monotonicity and a Taylor lower bound for the exponential. -/
noncomputable section
namespace ThresholdHC.UpperCost
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- The survival term at ratio `t ≥ 1` to the threshold scale `v`, in units of
`sqrt v`. -/
def tailTerm (v t : ℝ) : ℝ := Real.sqrt t * Real.exp (-2 * v * (Real.sqrt t - 1) ^ 2)

theorem tailTerm_nonneg (v t : ℝ) : 0 ≤ tailTerm v t :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- One band: the ratio lies in `[lo, hi]`, `ρ ≤ sqrt lo` and `sqrt hi ≤ h`. -/
theorem tailTerm_le_band {v v₀ t lo hi ρ h c : ℝ} (hv : v₀ ≤ v) (hv0 : 0 ≤ v₀) (hlo : lo ≤ t)
    (hhi : t ≤ hi) (hρ : 1 ≤ ρ) (hρlo : ρ ^ 2 ≤ lo) (hh : 0 < h) (hhh : hi ≤ h ^ 2)
    (htay : h ≤ c * ∑ i ∈ range 8, (2 * v₀ * (ρ - 1) ^ 2) ^ i / (i.factorial : ℝ)) :
    tailTerm v t ≤ c := by
  have ht0 : 0 ≤ t := (sq_nonneg ρ).trans (hρlo.trans hlo)
  have hsq : ρ ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (hρlo.trans hlo)
  have hst : Real.sqrt t ≤ h := by
    rw [Real.sqrt_le_left hh.le]
    linarith
  have hd : (ρ - 1) ^ 2 ≤ (Real.sqrt t - 1) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.2 hρ) (by linarith) 2
  have hexp : Real.exp (-2 * v * (Real.sqrt t - 1) ^ 2) ≤ Real.exp (-(2 * v₀ * (ρ - 1) ^ 2)) := by
    apply Real.exp_le_exp.2
    have h1 : v₀ * (ρ - 1) ^ 2 ≤ v * (Real.sqrt t - 1) ^ 2 :=
      mul_le_mul hv hd (sq_nonneg _) (hv0.trans hv)
    linarith
  have hE : Real.exp (-(2 * v₀ * (ρ - 1) ^ 2)) ≤ c / h :=
    exp_neg_le_of_taylor (by positivity) 8 (by
      rw [div_mul_eq_mul_div, le_div_iff₀ hh]
      linarith)
  unfold tailTerm
  calc
    _ ≤ h * Real.exp (-(2 * v₀ * (ρ - 1) ^ 2)) :=
      mul_le_mul hst hexp (Real.exp_pos _).le hh.le
    _ ≤ h * (c / h) := mul_le_mul_of_nonneg_left hE hh.le
    _ = c := by field_simp

/-- The geometric part: `(1 + sqrt 2)*sqrt s ≤ (1 + 141422/100000)*h` when
`s ≤ b ≤ h^2`. -/
theorem base_le {s b h : ℝ} (hb : s ≤ b) (hh : 0 ≤ h) (hhb : b ≤ h ^ 2) :
    (1 + Real.sqrt 2) * Real.sqrt s ≤ (1 + 141422 / 100000) * h := by
  have h2 : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hs' : Real.sqrt s ≤ h := by
    rw [Real.sqrt_le_left hh]
    linarith
  have h0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  nlinarith [Real.sqrt_nonneg 2]

/-- Past ratio one, each term is at most the `bump` term of `UpperWork`. -/
theorem tailTerm_le_bump {v t : ℝ} (hv : 1 ≤ v) (ht : 1 ≤ t) : tailTerm v t ≤ bump t := by
  have hst : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hexp : Real.exp (-2 * v * (Real.sqrt t - 1) ^ 2) ≤ Real.exp (-2 * (Real.sqrt t - 1) ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (Real.sqrt t - 1)]
  unfold tailTerm bump
  exact mul_le_mul hst hexp (Real.exp_pos _).le (by linarith)

/-- Keep the first four doubled terms; the rest add at most `1/80`. -/
theorem offset_reduce (s : ℝ) (h1 : 1 ≤ s) {v : ℝ} (hv : 1 ≤ v) (I : ℕ) :
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ range I, tailTerm v (2 ^ i * s) ≤
      (1 + Real.sqrt 2) * Real.sqrt s +
        (tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s)) + 1 / 80 := by
  have hnn : ∀ i : ℕ, 0 ≤ tailTerm v (2 ^ i * s) := fun i => tailTerm_nonneg v _
  have hsplit : ∑ i ∈ range I, tailTerm v (2 ^ i * s) ≤
      ∑ i ∈ range 4, tailTerm v (2 ^ i * s) + ∑ i ∈ range I, tailTerm v (2 ^ (4 + i) * s) := by
    rw [← Finset.sum_range_add]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ => hnn i)
  have htail : ∑ i ∈ range I, tailTerm v (2 ^ (4 + i) * s) ≤ 1 / 80 := by
    calc
      _ ≤ ∑ i ∈ range I, (1 / 160) * (1 / 2 : ℝ) ^ i := by
        apply sum_le_sum
        intro i _
        have hp : (16 : ℝ) * 2 ^ i = 2 ^ (4 + i) := by rw [pow_add]; norm_num
        have hpi : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        have h16 : 16 ≤ 2 ^ (4 + i) * s := by rw [← hp]; nlinarith
        refine ((tailTerm_le_bump hv (by linarith)).trans (bump_tail h16)).trans ?_
        rw [one_div_pow, ← hp]
        rw [div_mul_div_comm, one_mul]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      _ = (1 / 160) * ∑ i ∈ range I, (1 / 2 : ℝ) ^ i := by rw [mul_sum]
      _ ≤ (1 / 160) * 2 := by gcongr; exact sum_geometric_two_le I
      _ = 1 / 80 := by norm_num
  have h4 : ∑ i ∈ range 4, tailTerm v (2 ^ i * s) =
      tailTerm v s + tailTerm v (2 * s) + tailTerm v (4 * s) + tailTerm v (8 * s) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [h4] at hsplit
  linarith

/-- The offset sum for `v ≥ 169/100`, which covers `v = 1 + log 2`. -/
theorem offset_le_first (s : ℝ) (h1 : 1 ≤ s) (h2 : s ≤ 2) {v : ℝ} (hv : (169 / 100 : ℝ) ≤ v) (I : ℕ) :
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ range I, tailTerm v (2 ^ i * s) ≤ (89 / 20 : ℝ) := by
  have hv1 : 1 ≤ v := le_trans (by norm_num) hv
  have hsum := offset_reduce s h1 hv1 I
  refine hsum.trans ?_
  rcases le_or_gt s (43 / 40 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (43 / 40 : ℝ)) (h := (1037 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (1 : ℝ)) (hi := (43 / 40 : ℝ)) (ρ := (1 : ℝ)) (h := (1037 / 1000 : ℝ)) (c := (1037 / 1000 : ℝ))
      hv (by norm_num) h1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (2 : ℝ)) (hi := (43 / 20 : ℝ)) (ρ := (707 / 500 : ℝ)) (h := (1467 / 1000 : ℝ)) (c := (411 / 500 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (4 : ℝ)) (hi := (43 / 10 : ℝ)) (ρ := (2 : ℝ)) (h := (1037 / 500 : ℝ)) (c := (73 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (8 : ℝ)) (hi := (43 / 5 : ℝ)) (ρ := (707 / 250 : ℝ)) (h := (2933 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (23 / 20 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (23 / 20 : ℝ)) (h := (1073 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (43 / 40 : ℝ)) (hi := (23 / 20 : ℝ)) (ρ := (259 / 250 : ℝ)) (h := (1073 / 1000 : ℝ)) (c := (1069 / 1000 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (43 / 20 : ℝ)) (hi := (23 / 10 : ℝ)) (ρ := (733 / 500 : ℝ)) (h := (1517 / 1000 : ℝ)) (c := (729 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (43 / 10 : ℝ)) (hi := (23 / 5 : ℝ)) (ρ := (2073 / 1000 : ℝ)) (h := (429 / 200 : ℝ)) (c := (23 / 500 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (43 / 5 : ℝ)) (hi := (46 / 5 : ℝ)) (ρ := (733 / 250 : ℝ)) (h := (1517 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (49 / 40 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (49 / 40 : ℝ)) (h := (1107 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (23 / 20 : ℝ)) (hi := (49 / 40 : ℝ)) (ρ := (134 / 125 : ℝ)) (h := (1107 / 1000 : ℝ)) (c := (136 / 125 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (23 / 10 : ℝ)) (hi := (49 / 20 : ℝ)) (ρ := (379 / 250 : ℝ)) (h := (783 / 500 : ℝ)) (c := (637 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (23 / 5 : ℝ)) (hi := (49 / 10 : ℝ)) (ρ := (268 / 125 : ℝ)) (h := (1107 / 500 : ℝ)) (c := (29 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (46 / 5 : ℝ)) (hi := (49 / 5 : ℝ)) (ρ := (3033 / 1000 : ℝ)) (h := (3131 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (261 / 200 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (261 / 200 : ℝ)) (h := (1143 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (49 / 40 : ℝ)) (hi := (261 / 200 : ℝ)) (ρ := (553 / 500 : ℝ)) (h := (1143 / 1000 : ℝ)) (c := (1101 / 1000 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (49 / 20 : ℝ)) (hi := (261 / 100 : ℝ)) (ρ := (313 / 200 : ℝ)) (h := (202 / 125 : ℝ)) (c := (11 / 20 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (49 / 10 : ℝ)) (hi := (261 / 50 : ℝ)) (ρ := (2213 / 1000 : ℝ)) (h := (457 / 200 : ℝ)) (c := (19 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (49 / 5 : ℝ)) (hi := (261 / 25 : ℝ)) (ρ := (313 / 100 : ℝ)) (h := (404 / 125 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (139 / 100 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (139 / 100 : ℝ)) (h := (1179 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (261 / 200 : ℝ)) (hi := (139 / 100 : ℝ)) (ρ := (571 / 500 : ℝ)) (h := (1179 / 1000 : ℝ)) (c := (551 / 500 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (261 / 100 : ℝ)) (hi := (139 / 50 : ℝ)) (ρ := (323 / 200 : ℝ)) (h := (417 / 250 : ℝ)) (c := (93 / 200 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (261 / 50 : ℝ)) (hi := (139 / 25 : ℝ)) (ρ := (571 / 250 : ℝ)) (h := (1179 / 500 : ℝ)) (c := (3 / 250 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (261 / 25 : ℝ)) (hi := (278 / 25 : ℝ)) (ρ := (3231 / 1000 : ℝ)) (h := (667 / 200 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (149 / 100 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (149 / 100 : ℝ)) (h := (1221 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (139 / 100 : ℝ)) (hi := (149 / 100 : ℝ)) (ρ := (589 / 500 : ℝ)) (h := (1221 / 1000 : ℝ)) (c := (1097 / 1000 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (139 / 50 : ℝ)) (hi := (149 / 50 : ℝ)) (ρ := (1667 / 1000 : ℝ)) (h := (1727 / 1000 : ℝ)) (c := (48 / 125 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (139 / 25 : ℝ)) (hi := (149 / 25 : ℝ)) (ρ := (2357 / 1000 : ℝ)) (h := (1221 / 500 : ℝ)) (c := (7 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (278 / 25 : ℝ)) (hi := (298 / 25 : ℝ)) (ρ := (1667 / 500 : ℝ)) (h := (3453 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (8 / 5 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (8 / 5 : ℝ)) (h := (253 / 200 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (149 / 100 : ℝ)) (hi := (8 / 5 : ℝ)) (ρ := (61 / 50 : ℝ)) (h := (253 / 200 : ℝ)) (c := (43 / 40 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (149 / 50 : ℝ)) (hi := (16 / 5 : ℝ)) (ρ := (863 / 500 : ℝ)) (h := (1789 / 1000 : ℝ)) (c := (151 / 500 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (149 / 25 : ℝ)) (hi := (32 / 5 : ℝ)) (ρ := (2441 / 1000 : ℝ)) (h := (253 / 100 : ℝ)) (c := (1 / 250 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (298 / 25 : ℝ)) (hi := (64 / 5 : ℝ)) (ρ := (863 / 250 : ℝ)) (h := (1789 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (43 / 25 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (43 / 25 : ℝ)) (h := (164 / 125 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (8 / 5 : ℝ)) (hi := (43 / 25 : ℝ)) (ρ := (158 / 125 : ℝ)) (h := (164 / 125 : ℝ)) (c := (1037 / 1000 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (16 / 5 : ℝ)) (hi := (86 / 25 : ℝ)) (ρ := (447 / 250 : ℝ)) (h := (371 / 200 : ℝ)) (c := (57 / 250 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (32 / 5 : ℝ)) (hi := (172 / 25 : ℝ)) (ρ := (2529 / 1000 : ℝ)) (h := (2623 / 1000 : ℝ)) (c := (3 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (64 / 5 : ℝ)) (hi := (344 / 25 : ℝ)) (ρ := (3577 / 1000 : ℝ)) (h := (371 / 100 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (37 / 20 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (37 / 20 : ℝ)) (h := (1361 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (43 / 25 : ℝ)) (hi := (37 / 20 : ℝ)) (ρ := (1311 / 1000 : ℝ)) (h := (1361 / 1000 : ℝ)) (c := (491 / 500 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (86 / 25 : ℝ)) (hi := (37 / 10 : ℝ)) (ρ := (927 / 500 : ℝ)) (h := (481 / 250 : ℝ)) (c := (33 / 200 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (172 / 25 : ℝ)) (hi := (37 / 5 : ℝ)) (ρ := (1311 / 500 : ℝ)) (h := (2721 / 1000 : ℝ)) (c := (1 / 500 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (344 / 25 : ℝ)) (hi := (74 / 5 : ℝ)) (ρ := (3709 / 1000 : ℝ)) (h := (481 / 125 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (199 / 100 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (199 / 100 : ℝ)) (h := (1411 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (37 / 20 : ℝ)) (hi := (199 / 100 : ℝ)) (ρ := (34 / 25 : ℝ)) (h := (1411 / 1000 : ℝ)) (c := (911 / 1000 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (37 / 10 : ℝ)) (hi := (199 / 50 : ℝ)) (ρ := (1923 / 1000 : ℝ)) (h := (399 / 200 : ℝ)) (c := (57 / 500 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (37 / 5 : ℝ)) (hi := (199 / 25 : ℝ)) (ρ := (68 / 25 : ℝ)) (h := (1411 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (74 / 5 : ℝ)) (hi := (398 / 25 : ℝ)) (ρ := (3847 / 1000 : ℝ)) (h := (399 / 100 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  have e := base_le (s := s) (b := (2 : ℝ)) (h := (283 / 200 : ℝ)) h2 (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := s) (lo := (199 / 100 : ℝ)) (hi := (2 : ℝ)) (ρ := (141 / 100 : ℝ)) (h := (283 / 200 : ℝ)) (c := (401 / 500 : ℝ))
    hv (by norm_num) hp.le h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 2 * s) (lo := (199 / 50 : ℝ)) (hi := (4 : ℝ)) (ρ := (997 / 500 : ℝ)) (h := (2 : ℝ)) (c := (73 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 4 * s) (lo := (199 / 25 : ℝ)) (hi := (8 : ℝ)) (ρ := (2821 / 1000 : ℝ)) (h := (2829 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (169 / 100 : ℝ)) (t := 8 * s) (lo := (398 / 25 : ℝ)) (hi := (16 : ℝ)) (ρ := (3989 / 1000 : ℝ)) (h := (4 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

/-- The offset sum for `v ≥ 119/50`, which covers `v = 1 + j*log 2` for `j ≥ 2`. -/
theorem offset_le_rest (s : ℝ) (h1 : 1 ≤ s) (h2 : s ≤ 2) {v : ℝ} (hv : (119 / 50 : ℝ) ≤ v) (I : ℕ) :
    (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ range I, tailTerm v (2 ^ i * s) ≤ (17 / 4 : ℝ) := by
  have hv1 : 1 ≤ v := le_trans (by norm_num) hv
  have hsum := offset_reduce s h1 hv1 I
  refine hsum.trans ?_
  rcases le_or_gt s (217 / 200 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (217 / 200 : ℝ)) (h := (521 / 500 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (1 : ℝ)) (hi := (217 / 200 : ℝ)) (ρ := (1 : ℝ)) (h := (521 / 500 : ℝ)) (c := (521 / 500 : ℝ))
      hv (by norm_num) h1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (2 : ℝ)) (hi := (217 / 100 : ℝ)) (ρ := (707 / 500 : ℝ)) (h := (737 / 500 : ℝ)) (c := (163 / 250 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (4 : ℝ)) (hi := (217 / 50 : ℝ)) (ρ := (2 : ℝ)) (h := (521 / 250 : ℝ)) (c := (21 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (8 : ℝ)) (hi := (217 / 25 : ℝ)) (ρ := (707 / 250 : ℝ)) (h := (2947 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (47 / 40 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (47 / 40 : ℝ)) (h := (271 / 250 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (217 / 200 : ℝ)) (hi := (47 / 40 : ℝ)) (ρ := (1041 / 1000 : ℝ)) (h := (271 / 250 : ℝ)) (c := (269 / 250 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (217 / 100 : ℝ)) (hi := (47 / 20 : ℝ)) (ρ := (1473 / 1000 : ℝ)) (h := (1533 / 1000 : ℝ)) (c := (529 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (217 / 50 : ℝ)) (hi := (47 / 10 : ℝ)) (ρ := (2083 / 1000 : ℝ)) (h := (271 / 125 : ℝ)) (c := (11 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (217 / 25 : ℝ)) (hi := (47 / 5 : ℝ)) (ρ := (1473 / 500 : ℝ)) (h := (1533 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (127 / 100 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (127 / 100 : ℝ)) (h := (1127 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (47 / 40 : ℝ)) (hi := (127 / 100 : ℝ)) (ρ := (1083 / 1000 : ℝ)) (h := (1127 / 1000 : ℝ)) (c := (1091 / 1000 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (47 / 20 : ℝ)) (hi := (127 / 50 : ℝ)) (ρ := (383 / 250 : ℝ)) (h := (797 / 500 : ℝ)) (c := (83 / 200 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (47 / 10 : ℝ)) (hi := (127 / 25 : ℝ)) (ρ := (2167 / 1000 : ℝ)) (h := (1127 / 500 : ℝ)) (c := (3 / 500 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (47 / 5 : ℝ)) (hi := (254 / 25 : ℝ)) (ρ := (613 / 200 : ℝ)) (h := (797 / 250 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (11 / 8 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (11 / 8 : ℝ)) (h := (1173 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (127 / 100 : ℝ)) (hi := (11 / 8 : ℝ)) (ρ := (563 / 500 : ℝ)) (h := (1173 / 1000 : ℝ)) (c := (136 / 125 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (127 / 50 : ℝ)) (hi := (11 / 4 : ℝ)) (ρ := (1593 / 1000 : ℝ)) (h := (1659 / 1000 : ℝ)) (c := (39 / 125 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (127 / 25 : ℝ)) (hi := (11 / 2 : ℝ)) (ρ := (2253 / 1000 : ℝ)) (h := (1173 / 500 : ℝ)) (c := (3 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (254 / 25 : ℝ)) (hi := (11 : ℝ)) (ρ := (3187 / 1000 : ℝ)) (h := (3317 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (149 / 100 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (149 / 100 : ℝ)) (h := (1221 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (11 / 8 : ℝ)) (hi := (149 / 100 : ℝ)) (ρ := (293 / 250 : ℝ)) (h := (1221 / 1000 : ℝ)) (c := (1061 / 1000 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (11 / 4 : ℝ)) (hi := (149 / 50 : ℝ)) (ρ := (829 / 500 : ℝ)) (h := (1727 / 1000 : ℝ)) (c := (221 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (11 / 2 : ℝ)) (hi := (149 / 25 : ℝ)) (ρ := (469 / 200 : ℝ)) (h := (1221 / 500 : ℝ)) (c := (1 / 500 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (11 : ℝ)) (hi := (298 / 25 : ℝ)) (ρ := (829 / 250 : ℝ)) (h := (3453 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (81 / 50 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (81 / 50 : ℝ)) (h := (1273 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (149 / 100 : ℝ)) (hi := (81 / 50 : ℝ)) (ρ := (61 / 50 : ℝ)) (h := (1273 / 1000 : ℝ)) (c := (253 / 250 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (149 / 50 : ℝ)) (hi := (81 / 25 : ℝ)) (ρ := (863 / 500 : ℝ)) (h := (9 / 5 : ℝ)) (c := (37 / 250 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (149 / 25 : ℝ)) (hi := (162 / 25 : ℝ)) (ρ := (2441 / 1000 : ℝ)) (h := (1273 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (298 / 25 : ℝ)) (hi := (324 / 25 : ℝ)) (ρ := (863 / 250 : ℝ)) (h := (18 / 5 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (353 / 200 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (353 / 200 : ℝ)) (h := (1329 / 1000 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (81 / 50 : ℝ)) (hi := (353 / 200 : ℝ)) (ρ := (159 / 125 : ℝ)) (h := (1329 / 1000 : ℝ)) (c := (187 / 200 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (81 / 25 : ℝ)) (hi := (353 / 100 : ℝ)) (ρ := (9 / 5 : ℝ)) (h := (1879 / 1000 : ℝ)) (c := (91 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (162 / 25 : ℝ)) (hi := (353 / 50 : ℝ)) (ρ := (509 / 200 : ℝ)) (h := (1329 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (324 / 25 : ℝ)) (hi := (353 / 25 : ℝ)) (ρ := (18 / 5 : ℝ)) (h := (1879 / 500 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  rcases le_or_gt s (77 / 40 : ℝ) with hk | hp
  · have e := base_le (s := s) (b := (77 / 40 : ℝ)) (h := (347 / 250 : ℝ)) hk (by norm_num) (by norm_num)
    have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (353 / 200 : ℝ)) (hi := (77 / 40 : ℝ)) (ρ := (166 / 125 : ℝ)) (h := (347 / 250 : ℝ)) (c := (104 / 125 : ℝ))
      hv (by norm_num) hp.le hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (353 / 100 : ℝ)) (hi := (77 / 20 : ℝ)) (ρ := (939 / 500 : ℝ)) (h := (1963 / 1000 : ℝ)) (c := (13 / 250 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (353 / 50 : ℝ)) (hi := (77 / 10 : ℝ)) (ρ := (2657 / 1000 : ℝ)) (h := (111 / 40 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (353 / 25 : ℝ)) (hi := (77 / 5 : ℝ)) (ρ := (3757 / 1000 : ℝ)) (h := (157 / 40 : ℝ)) (c := (1 / 1000 : ℝ))
      hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num at e
    linarith
  have e := base_le (s := s) (b := (2 : ℝ)) (h := (283 / 200 : ℝ)) h2 (by norm_num) (by norm_num)
  have b0 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := s) (lo := (77 / 40 : ℝ)) (hi := (2 : ℝ)) (ρ := (1387 / 1000 : ℝ)) (h := (283 / 200 : ℝ)) (c := (347 / 500 : ℝ))
    hv (by norm_num) hp.le h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b1 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 2 * s) (lo := (77 / 20 : ℝ)) (hi := (4 : ℝ)) (ρ := (981 / 500 : ℝ)) (h := (2 : ℝ)) (c := (27 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b2 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 4 * s) (lo := (77 / 10 : ℝ)) (hi := (8 : ℝ)) (ρ := (1387 / 500 : ℝ)) (h := (2829 / 1000 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have b3 := tailTerm_le_band (v := v) (v₀ := (119 / 50 : ℝ)) (t := 8 * s) (lo := (77 / 5 : ℝ)) (hi := (16 : ℝ)) (ρ := (981 / 250 : ℝ)) (h := (4 : ℝ)) (c := (1 / 1000 : ℝ))
    hv (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num at e
  linarith

end ThresholdHC.UpperCost
