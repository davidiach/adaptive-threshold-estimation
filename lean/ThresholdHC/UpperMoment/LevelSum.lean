import ThresholdHC.UpperMoment.Disagreement
import ThresholdHC.UpperWork.LevelSum

/-! The level sum of the call second moment with the sharper disagreement bound.

The second moment of one call is `∑_l e_l/p_l` with `p_l = (1-r)*r^l`,
`r = 2^{-1/2}`, and `e_l ≤ min 1 ((113/100)/(cap l*d^2)^2)` (`Disagreement`).
Levels with `cap l*d^2 ≤ 1` are bounded with `1`, and the rest with the
second bound. With `q^2 = cap m*d^2` for the last level `m` of the first kind,
the two parts are at most `a*q/d` and `b/(q^3*d)`, where `a = 6 + 4*sqrt 2`
and `b = (113/100)*(2 + sqrt 2)*x/(1 - x)` with `x = sqrt 2/4`. Since
`q ∈ [7/10, 1]`, their sum is at most `(72/5)/d`. This replaces the
constant `23` of `Uniform713.Series`, which uses `3` in place of `113/100`. -/
noncomputable section
namespace ThresholdHC.UpperMoment
open Real Finset ThresholdHC.Uniform713

theorem inv_pLevel (l : ℕ) : (pLevel l)⁻¹ = (2 + Real.sqrt 2) * Real.sqrt 2 ^ l := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have hr := UpperWork.rLevel_mul_sqrt_two
  have hrl : rLevel ^ l * Real.sqrt 2 ^ l = 1 := by rw [← mul_pow, hr, one_pow]
  have h1r : (1 - rLevel) * (2 + Real.sqrt 2) = 1 := by
    have hr' : rLevel = Real.sqrt 2 / 2 := by
      rw [eq_div_iff two_ne_zero]
      linear_combination (Real.sqrt 2) * hr - rLevel * hσ
    rw [hr']
    linear_combination (-1 / 2) * hσ
  unfold pLevel
  rw [mul_inv]
  rw [inv_eq_of_mul_eq_one_right h1r, inv_eq_of_mul_eq_one_right hrl]

/-- The levels bounded with `1`: exactly `(6 + 4*sqrt 2)*sqrt 2^n - (4 + 3*sqrt 2)`. -/
theorem inv_pLevel_sum (n : ℕ) :
    ∑ l ∈ range (n + 1), (pLevel l)⁻¹ =
      (6 + 4 * Real.sqrt 2) * Real.sqrt 2 ^ n - (4 + 3 * Real.sqrt 2) := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp_rw [inv_pLevel]
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    linear_combination (-3 * Real.sqrt 2 ^ n) * hσ

theorem geom_tail_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑ i ∈ range n, x ^ (i + 1) ≤ x / (1 - x) := by
  have hs := (hasSum_geometric_of_lt_one hx0 hx1).mul_left x
  have h := sum_le_hasSum (range n) (fun i _ => mul_nonneg hx0 (pow_nonneg hx0 i)) hs
  simpa [pow_succ, mul_comm, div_eq_mul_inv] using h

/-- The sharper level sum of the call second moment. -/
theorem secondMoment_levelSum_le (L : ℕ) (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1 / 2)
    (e : ℕ → ℝ) (he : ∀ l ≤ L, e l ≤ min 1 ((113 / 100) / (cap l * d ^ 2) ^ 2)) :
    ∑ l ∈ range (L + 1), e l / pLevel l ≤ (72 / 5) * min (Real.sqrt (cap L)) d⁻¹ := by
  classical
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hp : ∀ l, 0 < pLevel l := fun l => mul_pos (sub_pos.2 rLevel_lt_one) (pow_pos rLevel_pos l)
  have hd2 : 0 < d ^ 2 := by positivity
  have hsc : ∀ l, Real.sqrt (cap l) = Real.sqrt 2 ^ l := UpperWork.sqrt_cap
  -- the terms bounded with one
  have hpre : ∀ n, n ≤ L → ∑ l ∈ range (n + 1), e l / pLevel l ≤
      (6 + 4 * Real.sqrt 2) * Real.sqrt (cap n) := by
    intro n hn
    calc
      _ ≤ ∑ l ∈ range (n + 1), (pLevel l)⁻¹ := by
        apply sum_le_sum
        intro l hl
        have hl' : l ≤ L := by have := mem_range.1 hl; omega
        rw [div_eq_mul_inv]
        have h1 : e l ≤ 1 := (he l hl').trans (min_le_left _ _)
        have := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (hp l).le)
        linarith
      _ ≤ _ := by rw [inv_pLevel_sum, hsc]; linarith
  by_cases hL : cap L * d ^ 2 ≤ 1
  · refine (hpre L le_rfl).trans ?_
    have hmin : min (Real.sqrt (cap L)) d⁻¹ = Real.sqrt (cap L) := by
      apply min_eq_left
      rw [← one_div, le_div_iff₀ hd]
      have h : Real.sqrt (cap L) * d = Real.sqrt (cap L * d ^ 2) := by
        rw [Real.sqrt_mul (cap_pos L).le, Real.sqrt_sq hd.le]
      rw [h]
      exact Real.sqrt_le_one.mpr hL
    rw [hmin]
    have := Real.sqrt_nonneg (cap L)
    nlinarith
  · have hL' : 1 < cap L * d ^ 2 := lt_of_not_ge hL
    have hex : ∃ k, 1 < cap k * d ^ 2 := ⟨L, hL'⟩
    have hK1L : Nat.find hex ≤ L := Nat.find_min' hex hL'
    have hK1 : Nat.find hex ≠ 0 := by
      intro h0
      have h := Nat.find_spec hex
      rw [h0, cap_zero, one_mul] at h
      nlinarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hK1
    have hθhi : cap m * d ^ 2 ≤ 1 := not_lt.1 (Nat.find_min hex (by omega))
    have hθlo : 1 / 2 < cap m * d ^ 2 := by
      have h := Nat.find_spec hex
      rw [hm, cap_succ] at h
      linarith
    have hmL : m + 1 ≤ L := by omega
    have hsm : 0 < Real.sqrt (cap m) := Real.sqrt_pos.2 (cap_pos m)
    set q := Real.sqrt (cap m) * d with hq_def
    have hq2 : q ^ 2 = cap m * d ^ 2 := by rw [hq_def, mul_pow, Real.sq_sqrt (cap_pos m).le]
    have hq0 : 0 < q := mul_pos hsm hd
    have hq7 : 7 / 10 ≤ q := by nlinarith
    have hq1 : q ≤ 1 := by nlinarith
    have hsplit : L + 1 = (m + 1) + (L - m) := by omega
    rw [hsplit, sum_range_add]
    have hP : ∑ l ∈ range (m + 1), e l / pLevel l ≤ (6 + 4 * Real.sqrt 2) * (q / d) := by
      refine (hpre m (by omega)).trans (le_of_eq ?_)
      rw [hq_def]
      field_simp
    -- the terms bounded with the disagreement bound
    set x := Real.sqrt 2 / 4 with hx_def
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x < 1 := by rw [hx_def]; linarith
    have hT : ∑ i ∈ range (L - m), e (m + 1 + i) / pLevel (m + 1 + i) ≤
        ((113 / 100) * (2 + Real.sqrt 2) * Real.sqrt 2 ^ m / (q ^ 2) ^ 2) *
          ∑ i ∈ range (L - m), x ^ (i + 1) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have hi' := mem_range.1 hi
      have hl : m + 1 + i ≤ L := by omega
      have hcapl : cap (m + 1 + i) * d ^ 2 = 2 ^ (i + 1) * q ^ 2 := by
        rw [hq2]
        simp only [cap]
        ring
      have he' : e (m + 1 + i) ≤ (113 / 100) / (2 ^ (i + 1) * q ^ 2) ^ 2 := by
        have h := (he (m + 1 + i) hl).trans (min_le_right _ _)
        rwa [hcapl] at h
      rw [div_eq_mul_inv, inv_pLevel]
      have hinv0 : 0 ≤ (2 + Real.sqrt 2) * Real.sqrt 2 ^ (m + 1 + i) := by positivity
      calc
        e (m + 1 + i) * ((2 + Real.sqrt 2) * Real.sqrt 2 ^ (m + 1 + i)) ≤
            (113 / 100) / (2 ^ (i + 1) * q ^ 2) ^ 2 *
              ((2 + Real.sqrt 2) * Real.sqrt 2 ^ (m + 1 + i)) :=
          mul_le_mul_of_nonneg_right he' hinv0
        _ = _ := by
          have h4 : (4 : ℝ) ^ (i + 1) = 2 ^ (i + 1) * 2 ^ (i + 1) := by
            rw [← mul_pow]
            norm_num
          have hpow : Real.sqrt 2 ^ (m + 1 + i) = Real.sqrt 2 ^ m * Real.sqrt 2 ^ (i + 1) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hx_def, div_pow, h4, hpow]
          field_simp
    have hG := geom_tail_le (L - m) hx0 hx1
    have hc0 : 0 ≤ (113 / 100) * (2 + Real.sqrt 2) * Real.sqrt 2 ^ m / (q ^ 2) ^ 2 := by
      positivity
    have hT' := hT.trans (mul_le_mul_of_nonneg_left hG hc0)
    have hsm' : Real.sqrt 2 ^ m = q / d := by
      rw [hq_def, ← hsc m]
      field_simp
    set b := (113 / 100) * (2 + Real.sqrt 2) * (x / (1 - x)) with hb_def
    have hTb : (113 / 100) * (2 + Real.sqrt 2) * Real.sqrt 2 ^ m / (q ^ 2) ^ 2 * (x / (1 - x)) =
        b / (q ^ 3 * d) := by
      rw [hsm', hb_def]
      field_simp
    rw [hTb] at hT'
    -- numerical bounds on the two constants
    have ha : 6 + 4 * Real.sqrt 2 ≤ 11657 / 1000 := by linarith
    have hxu : x ≤ 35356 / 100000 := by rw [hx_def]; linarith
    have hxr : x / (1 - x) ≤ 547 / 1000 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hb : b ≤ 53 / 25 := by
      rw [hb_def]
      have h2 : 0 ≤ 2 + Real.sqrt 2 := by positivity
      have hxr0 : 0 ≤ x / (1 - x) := div_nonneg hx0 (by linarith)
      nlinarith [mul_le_mul (show 2 + Real.sqrt 2 ≤ 341422 / 100000 by linarith) hxr hxr0
        (by norm_num)]
    have hpoly : (11657 / 1000) * q + (53 / 25) / q ^ 3 ≤ 72 / 5 := by
      have hq3 : 0 < q ^ 3 := by positivity
      rw [← sub_nonneg]
      have hQ : 0 ≤ (11657 / 1000) * q ^ 2 + (17 / 10 * (11657 / 1000) - 72 / 5) * q +
          (17 / 10 * (17 / 10 * (11657 / 1000) - 72 / 5) - 7 / 10 * (11657 / 1000)) := by
        nlinarith
      have hprod := mul_nonneg (mul_nonneg (sub_nonneg.2 hq7) (sub_nonneg.2 hq1)) hQ
      have he : 72 / 5 - ((11657 / 1000) * q + (53 / 25) / q ^ 3) =
          (72 / 5 * q ^ 3 - (11657 / 1000) * q ^ 4 - 53 / 25) / q ^ 3 := by
        field_simp
        ring
      rw [he]
      apply div_nonneg _ hq3.le
      nlinarith [hprod]
    have hmin : min (Real.sqrt (cap L)) d⁻¹ = d⁻¹ := by
      apply min_eq_right
      rw [← one_div, div_le_iff₀ hd]
      have h : Real.sqrt (cap L) * d = Real.sqrt (cap L * d ^ 2) := by
        rw [Real.sqrt_mul (cap_pos L).le, Real.sqrt_sq hd.le]
      rw [h]
      exact Real.le_sqrt_of_sq_le (by linarith)
    rw [hmin]
    have hb0 : 0 ≤ b := by rw [hb_def]; positivity
    calc
      _ ≤ (6 + 4 * Real.sqrt 2) * (q / d) + b / (q ^ 3 * d) := add_le_add hP hT'
      _ ≤ (11657 / 1000) * (q / d) + (53 / 25) / (q ^ 3 * d) := by
        gcongr
      _ = ((11657 / 1000) * q + (53 / 25) / q ^ 3) / d := by field_simp
      _ ≤ (72 / 5) / d := div_le_div_of_nonneg_right hpoly hd.le
      _ = _ := by rw [div_eq_mul_inv]

end ThresholdHC.UpperMoment
