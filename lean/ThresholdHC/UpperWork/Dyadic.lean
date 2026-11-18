import ThresholdHC.Uniform713.Common

/-! Deterministic dyadic sums behind the sharper expected-work bound.

Past the stopping scale, the survival term at the dyadic cap with ratio `s`
to the stopping scale is at most `bump s = s*exp(-2*(sqrt s-1)^2)` in units of
that scale. With `s` the first ratio above one, the work sum is at most
`s + ∑_j bump (2^j*s)`, which `offset_sum_le` bounds by `49/10` for every
`s` in `(1, 2]`. The proof splits `(1, 2]` into four pieces and bounds the
first four doubled terms on each piece by monotonicity and a Taylor lower
bound for the exponential; `bump_tail` bounds the rest. -/
noncomputable section
namespace ThresholdHC.UpperWork
open Real Finset ThresholdHC.Uniform713

/-- The dyadic survival term past the stopping scale, at ratio `s`. -/
def bump (s : ℝ) : ℝ := s * Real.exp (-2 * (Real.sqrt s - 1) ^ 2)

theorem bump_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ bump s :=
  mul_nonneg hs (Real.exp_pos _).le

theorem exp_neg_le_of_taylor {v c : ℝ} (hv : 0 ≤ v) (n : ℕ)
    (h : 1 ≤ c * ∑ i ∈ range n, v ^ i / (i.factorial : ℝ)) : Real.exp (-v) ≤ c := by
  have hT := Real.sum_le_exp_of_nonneg hv n
  have hT0 : 0 ≤ ∑ i ∈ range n, v ^ i / (i.factorial : ℝ) :=
    sum_nonneg (fun i _ => by positivity)
  have hc : 0 ≤ c := by
    by_contra hneg
    have hlt := lt_of_not_ge hneg
    nlinarith
  have h1 : 1 ≤ c * Real.exp v := h.trans (mul_le_mul_of_nonneg_left hT hc)
  rw [Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀ (Real.exp_pos v)).2 h1

/-- A crude bound on one band: the ratio is at most `hi`, and the exponent is
at least its value at a lower bound `ρ` of the square root. -/
theorem bump_le_band {t lo hi ρ c : ℝ} (hlo : lo ≤ t) (hhi : t ≤ hi) (hρ : 1 ≤ ρ)
    (hρlo : ρ ^ 2 ≤ lo)
    (htay : hi ≤ c * ∑ i ∈ range 8, (2 * (ρ - 1) ^ 2) ^ i / (i.factorial : ℝ)) :
    bump t ≤ c := by
  have hρ2 : 1 ≤ ρ ^ 2 := by nlinarith
  have ht1 : 1 ≤ t := by linarith
  have hhi0 : 0 < hi := by linarith
  have hsq : ρ ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (hρlo.trans hlo)
  have hv : (ρ - 1) ^ 2 ≤ (Real.sqrt t - 1) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.2 hρ) (by linarith) 2
  have hexp : Real.exp (-2 * (Real.sqrt t - 1) ^ 2) ≤ Real.exp (-2 * (ρ - 1) ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  have hE : Real.exp (-2 * (ρ - 1) ^ 2) ≤ c / hi := by
    have h := exp_neg_le_of_taylor (v := 2 * (ρ - 1) ^ 2) (c := c / hi) (by positivity) 8 (by
      rw [div_mul_eq_mul_div, le_div_iff₀ hhi0]
      linarith)
    simpa [neg_mul] using h
  unfold bump
  calc
    _ ≤ hi * Real.exp (-2 * (ρ - 1) ^ 2) := mul_le_mul hhi hexp (Real.exp_pos _).le hhi0.le
    _ ≤ hi * (c / hi) := mul_le_mul_of_nonneg_left hE hhi0.le
    _ = c := by field_simp

/-- Far past the stopping scale the terms are negligible. -/
theorem bump_tail {t : ℝ} (ht : 16 ≤ t) : bump t ≤ 1 / (10 * t) := by
  have ht0 : 0 ≤ t := by linarith
  set r := Real.sqrt t with hr_def
  have hr : 4 ≤ r := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have htr : t = r ^ 2 := (Real.sq_sqrt ht0).symm
  have hv : 0 ≤ 2 * (r - 1) ^ 2 := by positivity
  have hE := Real.pow_div_factorial_le_exp (2 * (r - 1) ^ 2) hv 4
  have hw : (9 / 16) * r ^ 2 ≤ (r - 1) ^ 2 := by nlinarith
  have hw4 : ((9 / 16) * r ^ 2) ^ 4 ≤ ((r - 1) ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hw 4
  have hr4 : 256 ≤ r ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hr 4
    norm_num at h
    linarith
  have hr40 : 0 < r ^ 4 := by positivity
  have key : 10 * r ^ 4 ≤ (2 * (r - 1) ^ 2) ^ 4 / (Nat.factorial 4 : ℝ) := by
    have he : (2 * (r - 1) ^ 2) ^ 4 / (Nat.factorial 4 : ℝ) = (2 / 3) * ((r - 1) ^ 2) ^ 4 := by
      norm_num [Nat.factorial]
      ring
    have h8 : ((9 / 16) * r ^ 2) ^ 4 = (9 / 16) ^ 4 * r ^ 4 * r ^ 4 := by ring
    rw [he]
    have hm : (9 / 16 : ℝ) ^ 4 * 256 * r ^ 4 ≤ (9 / 16) ^ 4 * r ^ 4 * r ^ 4 := by
      have := mul_le_mul_of_nonneg_left hr4 (by positivity : (0 : ℝ) ≤ (9 / 16) ^ 4 * r ^ 4)
      nlinarith
    nlinarith
  have hexp : Real.exp (-2 * (r - 1) ^ 2) ≤ 1 / (10 * r ^ 4) := by
    rw [neg_mul, Real.exp_neg, one_div]
    apply inv_anti₀ (by positivity)
    linarith
  unfold bump
  rw [← hr_def]
  calc
    _ ≤ t * (1 / (10 * r ^ 4)) := mul_le_mul_of_nonneg_left hexp ht0
    _ = 1 / (10 * t) := by
      rw [htr]
      field_simp

/-- The offset sum: for every ratio `s` in `(1, 2]`, the first ratio above one,
the remaining dyadic terms together with `s` are at most `49/10`. -/
theorem offset_sum_le (s : ℝ) (h1 : 1 < s) (h2 : s ≤ 2) (J : ℕ) :
    s + ∑ j ∈ range J, bump (2 ^ j * s) ≤ 49 / 10 := by
  have hs0 : 0 ≤ s := by linarith
  have hnn : ∀ j : ℕ, 0 ≤ bump (2 ^ j * s) := fun j => bump_nonneg (by positivity)
  have hsplit : ∑ j ∈ range J, bump (2 ^ j * s) ≤
      ∑ j ∈ range 4, bump (2 ^ j * s) + ∑ j ∈ range J, bump (2 ^ (4 + j) * s) := by
    rw [← Finset.sum_range_add]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => hnn j)
  have htail : ∑ j ∈ range J, bump (2 ^ (4 + j) * s) ≤ 1 / 80 := by
    calc
      _ ≤ ∑ j ∈ range J, (1 / 160) * (1 / 2 : ℝ) ^ j := by
        apply sum_le_sum
        intro j _
        have hp : (16 : ℝ) * 2 ^ j = 2 ^ (4 + j) := by rw [pow_add]; norm_num
        have hpj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have h16 : 16 ≤ 2 ^ (4 + j) * s := by rw [← hp]; nlinarith
        refine (bump_tail h16).trans ?_
        rw [one_div_pow, ← hp]
        rw [div_mul_div_comm, one_mul]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      _ = (1 / 160) * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j := by rw [mul_sum]
      _ ≤ (1 / 160) * 2 := by gcongr; exact sum_geometric_two_le J
      _ = 1 / 80 := by norm_num
  have h4 : ∑ j ∈ range 4, bump (2 ^ j * s) =
      bump s + bump (2 * s) + bump (4 * s) + bump (8 * s) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [h4] at hsplit
  have hsum : s + ∑ j ∈ range J, bump (2 ^ j * s) ≤
      s + (bump s + bump (2 * s) + bump (4 * s) + bump (8 * s)) + 1 / 80 := by linarith
  refine hsum.trans ?_
  rcases le_or_gt s (7 / 6) with ha | ha
  · have b0 := bump_le_band (t := s) (lo := 1) (hi := 7 / 6) (ρ := 1) (c := 7 / 6)
      h1.le ha le_rfl (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := bump_le_band (t := 2 * s) (lo := 2) (hi := 7 / 3) (ρ := 141 / 100)
      (c := 167 / 100) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := bump_le_band (t := 4 * s) (lo := 4) (hi := 14 / 3) (ρ := 2)
      (c := 16 / 25) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := bump_le_band (t := 8 * s) (lo := 8) (hi := 28 / 3) (ρ := 141 / 50)
      (c := 1 / 50) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    linarith
  rcases le_or_gt s (7 / 5) with hb | hb
  · have b0 := bump_le_band (t := s) (lo := 7 / 6) (hi := 7 / 5) (ρ := 27 / 25)
      (c := 139 / 100) ha.le hb (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := bump_le_band (t := 2 * s) (lo := 7 / 3) (hi := 14 / 5) (ρ := 38 / 25)
      (c := 41 / 25) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := bump_le_band (t := 4 * s) (lo := 14 / 3) (hi := 28 / 5) (ρ := 54 / 25)
      (c := 39 / 100) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := bump_le_band (t := 8 * s) (lo := 28 / 3) (hi := 56 / 5) (ρ := 61 / 20)
      (c := 1 / 100) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    linarith
  rcases le_or_gt s (5 / 3) with hc | hc
  · have b0 := bump_le_band (t := s) (lo := 7 / 5) (hi := 5 / 3) (ρ := 59 / 50)
      (c := 157 / 100) hb.le hc (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := bump_le_band (t := 2 * s) (lo := 14 / 5) (hi := 10 / 3) (ρ := 167 / 100)
      (c := 34 / 25) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := bump_le_band (t := 4 * s) (lo := 28 / 5) (hi := 20 / 3) (ρ := 59 / 25)
      (c := 9 / 50) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := bump_le_band (t := 8 * s) (lo := 56 / 5) (hi := 40 / 3) (ρ := 167 / 50)
      (c := 1 / 100) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    linarith
  · have b0 := bump_le_band (t := s) (lo := 5 / 3) (hi := 2) (ρ := 129 / 100)
      (c := 17 / 10) hc.le h2 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b1 := bump_le_band (t := 2 * s) (lo := 10 / 3) (hi := 4) (ρ := 91 / 50)
      (c := 21 / 20) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b2 := bump_le_band (t := 4 * s) (lo := 20 / 3) (hi := 8) (ρ := 129 / 50)
      (c := 7 / 100) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have b3 := bump_le_band (t := 8 * s) (lo := 40 / 3) (hi := 16) (ρ := 73 / 20)
      (c := 1 / 100) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    linarith

end ThresholdHC.UpperWork
