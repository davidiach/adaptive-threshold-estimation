import ThresholdHC.UpperCost.Grid
import ThresholdHC.UpperWork.Survival

/-! The level sum of the padded call cost.

A call at level `l ≤ L` costs at most `1 + ∑_{k<l} cap k*P(survive check k)`, and
the survival probability at check `k` of the cap-`2^l` classifier is at most
`survivalBound l k d` (`UpperWork.Survival`). The threshold of that check
depends on `l` and `k` only through `j = l - k`: it is below `d` exactly when
`cap k*d^2 ≥ v_j = 1 + j*log 2`. Summing over pairs `(l, k)` with a fixed
difference therefore follows one dyadic grid (`Grid`), weighted by
`(1 - r)*r^j`, with `r = 2^{-1/2}`. The offset bounds `89/20` for `j = 1` and
`17/4` for `j ≥ 2`, and `sqrt v_j ≤ (v_j + 4)/4`, give the constant `11/2`.
The geometric extension of each grid covers the levels above `L`, which the
padded call charges one flip each. So the padded call cost is at most
`(11/2)*min (sqrt (2^L)) d⁻¹`, in place of `248/25 + 1 = 273/25`. -/
noncomputable section
namespace ThresholdHC.UpperCost
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- Summing over pairs `k < l ≤ L` by the difference `l - k - 1`. -/
theorem sum_triangle (L : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ l ∈ range (L + 1), ∑ k ∈ range l, F l k =
      ∑ j ∈ range L, ∑ k ∈ range (L - j), F (k + j + 1) k := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih]
    have h1 : ∀ j ∈ range (L + 1), ∑ k ∈ range (L + 1 - j), F (k + j + 1) k =
        ∑ k ∈ range (L - j), F (k + j + 1) k + F (L + 1) (L - j) := by
      intro j hj
      have hj' := mem_range.1 hj
      rw [show L + 1 - j = (L - j) + 1 by omega, sum_range_succ]
      congr 2
      omega
    rw [sum_congr rfl h1, sum_add_distrib, sum_range_succ (fun j => ∑ k ∈ range (L - j), _) L]
    simp only [Nat.sub_self, range_zero, sum_empty, add_zero]
    congr 1
    rw [← sum_range_reflect (fun k => F (L + 1) k) (L + 1)]
    apply sum_congr rfl
    intro j hj
    congr 1

/-- The threshold scale of the check `k` of the cap-`2^(k+J)` classifier. -/
theorem survivalBound_eq_grid (k J : ℕ) {d : ℝ} (hd : 0 < d) :
    survivalBound (k + J) k d = gridSurvival (1 + J * Real.log 2) (cap k * d ^ 2) := by
  have hc := cap_pos k
  have hratio : cap (k + J) / cap k = 2 ^ J := by
    simp only [cap, pow_add]
    field_simp
  have hlog : Real.log (cap (k + J) / cap k) = J * Real.log 2 := by
    rw [hratio, Real.log_pow]
  set v := 1 + (J : ℝ) * Real.log 2 with hv
  have hv0 : 0 ≤ v := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have ht : Tier2.Model.threshold1 (cap k) (cap (k + J)) = Real.sqrt (v / cap k) := by
    unfold Tier2.Model.threshold1
    rw [hlog]
  have hcond : Real.sqrt (v / cap k) ≤ d ↔ v ≤ cap k * d ^ 2 := by
    rw [Real.sqrt_le_left hd.le, div_le_iff₀ hc, mul_comm]
  have hexp : cap k * (d - Real.sqrt (v / cap k)) ^ 2 =
      (Real.sqrt (cap k * d ^ 2) - Real.sqrt v) ^ 2 := by
    have hs : Real.sqrt v = Real.sqrt (cap k) * Real.sqrt (v / cap k) := by
      rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq hd.le, hs]
    have hc' : Real.sqrt (cap k) ^ 2 = cap k := Real.sq_sqrt hc.le
    rw [show (Real.sqrt (cap k) * d - Real.sqrt (cap k) * Real.sqrt (v / cap k)) ^ 2 =
      Real.sqrt (cap k) ^ 2 * (d - Real.sqrt (v / cap k)) ^ 2 by ring, hc']
  unfold survivalBound gridSurvival
  rw [ht]
  by_cases h : v ≤ cap k * d ^ 2
  · rw [ite_eq_left (hcond.2 h), ite_eq_left h]
    congr 1
    rw [mul_assoc, hexp]
  · rw [ite_eq_right (fun h' => h (hcond.1 h')), ite_eq_right h]

theorem log_two_bounds :
    (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 6931471808 / 10000000000 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

/-- The constant of the reordered sum: at most `11/2`. -/
theorem cost_constant_le (L : ℕ) :
    ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) *
      (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) * (if j = 0 then 89 / 20 else 17 / 4)) ≤
      11 / 2 := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : rLevel = Real.sqrt 2 / 2 := by
    unfold rLevel
    field_simp
    linarith
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  obtain ⟨hl0, hl1⟩ := log_two_bounds
  cases L with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    simp only [Nat.succ_ne_zero, ite_false, CharP.cast_eq_zero, zero_add, ite_true, pow_one]
    -- the term `j = 0`
    have hs1 : Real.sqrt (1 + 1 * Real.log 2) ≤ 130122 / 100000 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith
    have hfirst : (1 - rLevel) * rLevel * (Real.sqrt (1 + 1 * Real.log 2) * (89 / 20)) ≤
        (20711 / 100000) * (130122 / 100000) * (89 / 20) := by
      have hc : (1 - rLevel) * rLevel ≤ 20711 / 100000 := by rw [hr]; nlinarith
      have hc0 : 0 ≤ (1 - rLevel) * rLevel := mul_nonneg (by linarith) hr0.le
      have hs0 : 0 ≤ Real.sqrt (1 + 1 * Real.log 2) := Real.sqrt_nonneg _
      calc
        _ = ((1 - rLevel) * rLevel) * Real.sqrt (1 + 1 * Real.log 2) * (89 / 20) := by ring
        _ ≤ (20711 / 100000) * (130122 / 100000) * (89 / 20) := by
          gcongr
    -- the terms `j ≥ 1`, with `sqrt z ≤ (z + 4)/4`
    have hrest : ∑ i ∈ range n, (1 - rLevel) * rLevel ^ (i + 1 + 1) *
        (Real.sqrt (1 + (((i + 1 : ℕ) : ℝ) + 1) * Real.log 2) * (17 / 4)) ≤
        (17 / 4) * rLevel ^ 2 * ((5 + Real.log 2) / 4 + (Real.log 2 / 4) / (1 - rLevel)) := by
      have hterm : ∀ i ∈ range n, (1 - rLevel) * rLevel ^ (i + 1 + 1) *
          (Real.sqrt (1 + (((i + 1 : ℕ) : ℝ) + 1) * Real.log 2) * (17 / 4)) ≤
          ((17 / 4) * (1 - rLevel) * rLevel ^ 2) *
            (rLevel ^ i * ((5 + Real.log 2) / 4 + ((i : ℝ) + 1) * (Real.log 2 / 4))) := by
        intro i _
        have hz : Real.sqrt (1 + (((i + 1 : ℕ) : ℝ) + 1) * Real.log 2) ≤
            (5 + Real.log 2) / 4 + ((i : ℝ) + 1) * (Real.log 2 / 4) := by
          set z := 1 + (((i + 1 : ℕ) : ℝ) + 1) * Real.log 2 with hz
          have hz0 : 0 ≤ z := by positivity
          have hsz := Real.sq_sqrt hz0
          have hq : Real.sqrt z ≤ (z + 4) / 4 := by nlinarith [sq_nonneg (Real.sqrt z - 2)]
          refine hq.trans (le_of_eq ?_)
          rw [hz]
          push_cast
          ring
        have hw : 0 ≤ (1 - rLevel) * rLevel ^ (i + 1 + 1) :=
          mul_nonneg (by linarith) (pow_nonneg hr0.le _)
        calc
          _ ≤ (1 - rLevel) * rLevel ^ (i + 1 + 1) *
              (((5 + Real.log 2) / 4 + ((i : ℝ) + 1) * (Real.log 2 / 4)) * (17 / 4)) := by
            gcongr
          _ = _ := by ring
      refine (sum_le_sum hterm).trans ?_
      rw [← mul_sum]
      have hG := arith_geom_sum_le n (a := (5 + Real.log 2) / 4) (b := Real.log 2 / 4)
        (by positivity) (by positivity)
      have hk : 0 ≤ (17 / 4) * (1 - rLevel) * rLevel ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg hr0.le _)
      refine (mul_le_mul_of_nonneg_left hG hk).trans (le_of_eq ?_)
      have hne : 1 - rLevel ≠ 0 := by linarith
      field_simp
    have hval : (17 / 4) * rLevel ^ 2 * ((5 + Real.log 2) / 4 + (Real.log 2 / 4) / (1 - rLevel)) ≤
        (17 / 8) * ((56932 / 10000) / 4 + (6932 / 40000) * (341422 / 100000)) := by
      have hr2 : rLevel ^ 2 = 1 / 2 := by rw [hr]; nlinarith
      have hinv : 1 / (1 - rLevel) = 2 + Real.sqrt 2 := by
        rw [hr]
        have hne : 1 - Real.sqrt 2 / 2 ≠ 0 := by nlinarith
        rw [div_eq_iff hne]
        linear_combination (1 / 2) * hσ
      rw [hr2, div_eq_mul_one_div (Real.log 2 / 4), hinv]
      have hl4 : 0 ≤ Real.log 2 / 4 := by linarith
      nlinarith [mul_le_mul hl1 hσu (by linarith) (by norm_num)]
    norm_num at hfirst hval hrest ⊢
    linarith

/-- The padded call cost of the survival-form bound. -/
theorem padded_levelSum_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2) (w : ℕ → ℝ)
    (hw : ∀ l ≤ L, w l ≤ 1 + ∑ k ∈ range l, cap k * survivalBound l k d) :
    ∑ l ∈ range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (11 / 2) * min (Real.sqrt (cap L)) d⁻¹ := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hp : ∀ l, 0 ≤ pLevel l := fun l => mul_nonneg (by linarith) (pow_nonneg hr0.le l)
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrσ : rLevel * Real.sqrt 2 = 1 := rLevel_mul_sqrt_two
  -- each level costs at most its cap
  have hcapw : ∀ l ≤ L, w l ≤ cap l := by
    intro l hl
    refine (hw l hl).trans ?_
    have h : ∑ k ∈ range l, cap k * survivalBound l k d ≤ ∑ k ∈ range l, cap k :=
      sum_le_sum (fun k _ => mul_le_of_le_one_right (cap_pos k).le (survivalBound_le_one l k d))
    have hg : ∑ k ∈ range l, cap k = cap l - 1 := by
      change ∑ k ∈ range l, (2 : ℝ) ^ k = (2 : ℝ) ^ l - 1
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) l]
      norm_num
    linarith
  have hcapsum : ∑ l ∈ range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤ Real.sqrt (cap L) := by
    have h := sum_le_sum (fun l (hl : l ∈ range (L + 1)) => mul_le_mul_of_nonneg_left
      (hcapw l (Nat.le_of_lt_succ (mem_range.1 hl))) (hp l))
    rw [levelWeight_cap_sum, ← sqrt_cap] at h
    have hrL : rLevel ^ (L + 1) ≤ rLevel := by
      calc
        rLevel ^ (L + 1) ≤ rLevel ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
        _ = rLevel := pow_one _
    linarith
  have hsqrt : Real.sqrt (cap L) * d = Real.sqrt (cap L * d ^ 2) := by
    rw [Real.sqrt_mul (cap_pos L).le, Real.sqrt_sq hd.le]
  by_cases hsmall : cap L * d ^ 2 ≤ 16
  · refine hcapsum.trans ?_
    rw [mul_min_of_nonneg _ _ (by norm_num)]
    apply le_min
    · nlinarith [Real.sqrt_nonneg (cap L)]
    · have hs : Real.sqrt (cap L) * d ≤ 4 := by
        rw [hsqrt, Real.sqrt_le_left (by norm_num)]
        linarith
      rw [← div_eq_mul_inv, le_div_iff₀ hd]
      linarith
  · have hlarge : 16 < cap L * d ^ 2 := lt_of_not_ge hsmall
    have hmin : min (Real.sqrt (cap L)) d⁻¹ = d⁻¹ := by
      apply min_eq_right
      rw [← one_div, div_le_iff₀ hd, hsqrt]
      exact Real.le_sqrt_of_sq_le (by linarith)
    rw [hmin]
    -- at least three levels
    have hL3 : 3 ≤ L := by
      by_contra hL
      have hc : cap L ≤ 4 := by
        have h := Tier2.Model.cap_mono (show L ≤ 2 by omega)
        have h4 : cap 2 = 4 := by norm_num [cap]
        linarith
      have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [cap_pos L]
    -- reorder the double sum
    set v : ℕ → ℝ := fun j => 1 + ((j : ℝ) + 1) * Real.log 2 with hv
    set C : ℕ → ℝ := fun j => if j = 0 then 89 / 20 else 17 / 4 with hC
    have hlog := log_two_bounds
    have hgrid : ∀ j, ∑ k ∈ range (L - j), Real.sqrt (cap k * d ^ 2) *
        gridSurvival (v j) (cap k * d ^ 2) + d * (1 + Real.sqrt 2) ≤ Real.sqrt (v j) * C j := by
      intro j
      have hv1 : 1 ≤ v j := by simp only [hv]; nlinarith
      have hdv : d ^ 2 < v j := by nlinarith
      apply grid_sum_le hv1 hd hdv _ (L - j)
      intro s h1 h2 I
      by_cases hj : j = 0
      · simp only [hC, ite_eq_left hj]
        exact offset_le_first s h1 h2 (by simp only [hv, hj]; push_cast; nlinarith) I
      · simp only [hC, ite_eq_right hj]
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
        exact offset_le_rest s h1 h2 (by simp only [hv]; nlinarith) I
    -- the levels above `L` and the extension of each grid below `k = 0`
    have hpsum : ∑ l ∈ range (L + 1), pLevel l + rLevel ^ (L + 1) = 1 := by
      have hg := geom_sum_eq (ne_of_lt hr1) (L + 1)
      have hne : rLevel - 1 ≠ 0 := by linarith
      have h : ∑ l ∈ range (L + 1), pLevel l = (1 - rLevel) * ∑ l ∈ range (L + 1), rLevel ^ l := by
        rw [mul_sum]
        rfl
      rw [h, hg]
      field_simp
      ring
    have hwsum : ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) = rLevel * (1 - rLevel ^ L) := by
      have hg := geom_sum_eq (ne_of_lt hr1) L
      have hne : rLevel - 1 ≠ 0 := by linarith
      have h : ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) =
          (1 - rLevel) * rLevel * ∑ j ∈ range L, rLevel ^ j := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      rw [h, hg]
      field_simp
      ring
    have hext : 1 ≤ (1 + Real.sqrt 2) * (rLevel * (1 - rLevel ^ L)) := by
      have hrL : rLevel ^ L ≤ rLevel ^ 3 := pow_le_pow_of_le_one hr0.le hr1.le hL3
      have hr3 : rLevel ^ 3 = rLevel / 2 := by
        have hr2 : rLevel ^ 2 = 1 / 2 := by
          have : (rLevel * Real.sqrt 2) ^ 2 = 1 := by rw [hrσ]; norm_num
          rw [mul_pow, hσ] at this
          linarith
        rw [pow_succ, hr2]
        ring
      have hk : (1 + Real.sqrt 2) * rLevel = 1 + rLevel := by linear_combination hrσ
      have hrl : (7 : ℝ) / 10 ≤ rLevel := by
        have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
        nlinarith
      nlinarith
    -- reorder the double sum by the difference of levels
    have hterm : ∀ j k, d * pLevel (k + j + 1) * (cap k * survivalBound (k + j + 1) k d) =
        (1 - rLevel) * rLevel ^ (j + 1) *
          (Real.sqrt (cap k * d ^ 2) * gridSurvival (v j) (cap k * d ^ 2)) := by
      intro j k
      have hsb : survivalBound (k + j + 1) k d = gridSurvival (v j) (cap k * d ^ 2) := by
        rw [show k + j + 1 = k + (j + 1) by ring, survivalBound_eq_grid k (j + 1) hd]
        simp only [hv]
        push_cast
        ring_nf
      have hcap : rLevel ^ k * cap k = Real.sqrt 2 ^ k := by
        have h2 : cap k = Real.sqrt 2 ^ k * Real.sqrt 2 ^ k := by
          rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
          rfl
        rw [h2, ← mul_assoc, ← mul_pow, hrσ, one_pow, one_mul]
      rw [hsb, sqrt_cap_mul_sq k hd.le]
      unfold pLevel
      rw [show rLevel ^ (k + j + 1) = rLevel ^ (j + 1) * rLevel ^ k by ring]
      linear_combination ((1 - rLevel) * rLevel ^ (j + 1) * d *
        gridSurvival (v j) (cap k * d ^ 2)) * hcap
    have hdouble : d * ∑ l ∈ range (L + 1), pLevel l * w l ≤
        d * ∑ l ∈ range (L + 1), pLevel l +
          ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) *
            ∑ k ∈ range (L - j), Real.sqrt (cap k * d ^ 2) * gridSurvival (v j) (cap k * d ^ 2) := by
      have hb : ∑ l ∈ range (L + 1), pLevel l * w l ≤
          ∑ l ∈ range (L + 1), pLevel l * (1 + ∑ k ∈ range l, cap k * survivalBound l k d) :=
        sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left
          (hw l (Nat.le_of_lt_succ (mem_range.1 hl))) (hp l))
      have he : d * ∑ l ∈ range (L + 1), pLevel l * (1 + ∑ k ∈ range l, cap k * survivalBound l k d) =
          d * ∑ l ∈ range (L + 1), pLevel l +
            ∑ l ∈ range (L + 1), ∑ k ∈ range l, d * pLevel l * (cap k * survivalBound l k d) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro l _
        rw [← mul_sum]
        ring
      rw [sum_triangle L (fun l k => d * pLevel l * (cap k * survivalBound l k d))] at he
      simp only [hterm] at he
      simp only [← mul_sum] at he
      have := mul_le_mul_of_nonneg_left hb hd.le
      linarith
    have hgridsum : ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) *
          ∑ k ∈ range (L - j), Real.sqrt (cap k * d ^ 2) * gridSurvival (v j) (cap k * d ^ 2) ≤
        ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) * (Real.sqrt (v j) * C j) -
          d * (1 + Real.sqrt 2) * ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_le_sum
      intro j _
      have hw0 : 0 ≤ (1 - rLevel) * rLevel ^ (j + 1) := mul_nonneg (by linarith) (pow_nonneg hr0.le _)
      have := mul_le_mul_of_nonneg_left (hgrid j) hw0
      linarith
    have hconst := cost_constant_le L
    have hconst' : ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) * (Real.sqrt (v j) * C j) ≤ 11 / 2 :=
      hconst
    have hdp : d * (∑ l ∈ range (L + 1), pLevel l * w l + rLevel ^ (L + 1)) ≤ 11 / 2 := by
      rw [hwsum] at hgridsum
      have hpd : d * ∑ l ∈ range (L + 1), pLevel l + d * rLevel ^ (L + 1) = d := by
        rw [← mul_add, hpsum, mul_one]
      have hx : d ≤ d * ((1 + Real.sqrt 2) * (rLevel * (1 - rLevel ^ L))) := by
        nlinarith
      nlinarith
    rw [← div_eq_mul_inv, le_div_iff₀ hd]
    linarith

end ThresholdHC.UpperCost
