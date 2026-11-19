import ThresholdHC.UpperCallCost.Offset
import ThresholdHC.UpperDisagreement.LevelSum

/-! The level sum of the padded call cost with the constant `26/5`.

As in `UpperCost.LevelSum`, the survival terms of the call-cost sum are grouped
by the difference `j + 1` of the level and the check; each group follows one
dyadic grid with threshold scale `v_j = 1 + (j + 1)*log 2` and is at most
`sqrt v_j*C_j` minus its extension below the first check. `UpperCost` takes
`C_0 = 89/20`, `C_j = 17/4` for `j ≥ 1`, and `sqrt v ≤ (v + 4)/4`, which gives
`11/2`. Here `C_j = 399/100` for `j ≥ 2` (`offset_le_far`), the square roots of
the first eight scales are bounded one by one, and the rest by
`sqrt v ≤ (v + 9)/6`. The weighted sum of the offsets is then at most `26/5`
(`callCost_constant_le`), and the padded call cost at most
`(26/5)*min (sqrt (2^L)) d⁻¹` (`padded_levelSum_le`), or
`(26/5)*min (sqrt (2^L)) d⁻¹ - (21/5)*sqrt (2^L)` when `2^L*d^2 ≤ 1`
(`padded_regime_le`). -/
noncomputable section
namespace ThresholdHC.UpperCallCost
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork ThresholdHC.UpperCost

/-- The offset bound of the grid with level difference `j + 1`. -/
theorem callOffset_nonneg (j : ℕ) :
    0 ≤ (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100) := by
  split_ifs <;> norm_num

/-- One term of the weighted sum of the offsets. -/
theorem callTerm_le (j : ℕ) {w q c : ℝ}
    (hw : (1 - rLevel) * rLevel ^ (j + 1) ≤ w)
    (hq : 1 + ((j : ℝ) + 1) * Real.log 2 ≤ q ^ 2) (hq0 : 0 ≤ q)
    (hc : (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100) ≤ c) :
    (1 - rLevel) * rLevel ^ (j + 1) *
      (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) *
        (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100)) ≤ w * (q * c) := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hw0 : 0 ≤ (1 - rLevel) * rLevel ^ (j + 1) := mul_nonneg (by linarith) (pow_nonneg hr0.le _)
  have hs : Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) ≤ q := Real.sqrt_le_iff.2 ⟨hq0, hq⟩
  have hC0 := callOffset_nonneg j
  have h1 : Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) *
      (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100) ≤ q * c :=
    mul_le_mul hs hc hC0 hq0
  exact mul_le_mul hw h1 (mul_nonneg (Real.sqrt_nonneg _) hC0) (hw0.trans hw)

/-- The weights `(1 - r)*r^(j+1)` at odd and even powers. -/
theorem weight_odd (m : ℕ) : (1 - rLevel) * rLevel ^ (2 * m + 1) ≤ (20711 / 100000) * (1 / 2) ^ m := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrσ : rLevel * Real.sqrt 2 = 1 := rLevel_mul_sqrt_two
  have hr2 : rLevel ^ 2 = 1 / 2 := by
    have : (rLevel * Real.sqrt 2) ^ 2 = 1 := by rw [hrσ]; norm_num
    rw [mul_pow, hσ] at this
    linarith
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hru : rLevel ≤ 70711 / 100000 := by nlinarith [rLevel_pos]
  have hp : rLevel ^ (2 * m + 1) = rLevel * (1 / 2) ^ m := by
    rw [pow_succ, pow_mul, hr2]
    ring
  rw [hp]
  have hk : (1 - rLevel) * rLevel = rLevel - 1 / 2 := by nlinarith
  have hm : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
  calc
    (1 - rLevel) * (rLevel * (1 / 2) ^ m) = (rLevel - 1 / 2) * (1 / 2) ^ m := by rw [← hk]; ring
    _ ≤ (20711 / 100000) * (1 / 2) ^ m := mul_le_mul_of_nonneg_right (by linarith) hm

theorem weight_even (m : ℕ) : (1 - rLevel) * rLevel ^ (2 * m + 2) ≤ (2929 / 10000) * (1 / 2) ^ (m + 1) := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrσ : rLevel * Real.sqrt 2 = 1 := rLevel_mul_sqrt_two
  have hr2 : rLevel ^ 2 = 1 / 2 := by
    have : (rLevel * Real.sqrt 2) ^ 2 = 1 := by rw [hrσ]; norm_num
    rw [mul_pow, hσ] at this
    linarith
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hrl : 7071 / 10000 ≤ rLevel := by nlinarith [rLevel_pos]
  have hp : rLevel ^ (2 * m + 2) = (1 / 2) ^ (m + 1) := by
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, hr2]
  rw [hp]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The weighted sum of the offsets: at most `26/5`. -/
theorem callCost_constant_le (L : ℕ) :
    ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) *
      (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) *
        (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100)) ≤ 26 / 5 := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrσ : rLevel * Real.sqrt 2 = 1 := rLevel_mul_sqrt_two
  have hr2 : rLevel ^ 2 = 1 / 2 := by
    have : (rLevel * Real.sqrt 2) ^ 2 = 1 := by rw [hrσ]; norm_num
    rw [mul_pow, hσ] at this
    linarith
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  obtain ⟨hl0, hl1⟩ := log_two_bounds
  set f : ℕ → ℝ := fun j => (1 - rLevel) * rLevel ^ (j + 1) *
    (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) *
      (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100)) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hr0.le _))
    (mul_nonneg (Real.sqrt_nonneg _) (callOffset_nonneg j))
  have hext : ∑ j ∈ range L, f j ≤ ∑ j ∈ range (8 + L), f j :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun j _ _ => hf0 j)
  rw [sum_range_add] at hext
  refine hext.trans ?_
  -- the first eight terms
  have hfirst : ∑ j ∈ range 8, f j ≤
      (20711 / 100000) * ((130121 / 100000) * (89 / 20)) +
      (2929 / 10000) * (1 / 2) * ((154477 / 100000) * (17 / 4)) +
      (20711 / 100000) * (1 / 2) * ((175484 / 100000) * (399 / 100)) +
      (2929 / 10000) * (1 / 4) * ((194232 / 100000) * (399 / 100)) +
      (20711 / 100000) * (1 / 4) * ((211323 / 100000) * (399 / 100)) +
      (2929 / 10000) * (1 / 8) * ((227132 / 100000) * (399 / 100)) +
      (20711 / 100000) * (1 / 8) * ((241910 / 100000) * (399 / 100)) +
      (2929 / 10000) * (1 / 16) * ((255836 / 100000) * (399 / 100)) := by
    simp only [sum_range_succ, sum_range_zero, zero_add]
    have t0 := callTerm_le 0 (w := 20711 / 100000) (q := 130121 / 100000) (c := 89 / 20)
      (by have := weight_odd 0; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t1 := callTerm_le 1 (w := (2929 / 10000) * (1 / 2)) (q := 154477 / 100000) (c := 17 / 4)
      (by have := weight_even 0; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t2 := callTerm_le 2 (w := (20711 / 100000) * (1 / 2)) (q := 175484 / 100000) (c := 399 / 100)
      (by have := weight_odd 1; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t3 := callTerm_le 3 (w := (2929 / 10000) * (1 / 4)) (q := 194232 / 100000) (c := 399 / 100)
      (by have := weight_even 1; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t4 := callTerm_le 4 (w := (20711 / 100000) * (1 / 4)) (q := 211323 / 100000) (c := 399 / 100)
      (by have := weight_odd 2; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t5 := callTerm_le 5 (w := (2929 / 10000) * (1 / 8)) (q := 227132 / 100000) (c := 399 / 100)
      (by have := weight_even 2; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t6 := callTerm_le 6 (w := (20711 / 100000) * (1 / 8)) (q := 241910 / 100000) (c := 399 / 100)
      (by have := weight_odd 3; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t7 := callTerm_le 7 (w := (2929 / 10000) * (1 / 16)) (q := 255836 / 100000) (c := 399 / 100)
      (by have := weight_even 3; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have e : f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 ≤ _ :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add t0 t1) t2)
        t3) t4) t5) t6) t7
    exact e
  -- the rest, with `sqrt v ≤ (v + 9)/6`
  have hrest : ∑ i ∈ range L, f (8 + i) ≤
      (399 / 100) * (rLevel / 16) / 6 * ((10 + 8 * Real.log 2) + Real.log 2 * (2 + Real.sqrt 2)) := by
    have hr9 : rLevel ^ 9 = rLevel / 16 := by
      rw [show 9 = 2 * 4 + 1 by rfl, pow_succ, pow_mul, hr2]
      ring
    have hterm : ∀ i ∈ range L, f (8 + i) ≤
        ((399 / 100) * (1 - rLevel) * rLevel ^ 9 / 6) *
          (rLevel ^ i * ((10 + 8 * Real.log 2) + ((i : ℝ) + 1) * Real.log 2)) := by
      intro i _
      have hne0 : 8 + i ≠ 0 := by omega
      have hne1 : 8 + i ≠ 1 := by omega
      simp only [hf, hne0, hne1, ite_false]
      set z := 1 + (((8 + i : ℕ) : ℝ) + 1) * Real.log 2 with hz
      have hz0 : 0 ≤ z := by rw [hz]; positivity
      have hsz := Real.sq_sqrt hz0
      have hq : Real.sqrt z ≤ (z + 9) / 6 := by nlinarith [sq_nonneg (Real.sqrt z - 3)]
      have hzv : (z + 9) / 6 = ((10 + 8 * Real.log 2) + ((i : ℝ) + 1) * Real.log 2) / 6 := by
        rw [hz]
        push_cast
        ring
      have hw : 0 ≤ (1 - rLevel) * rLevel ^ (8 + i + 1) :=
        mul_nonneg (by linarith) (pow_nonneg hr0.le _)
      calc
        _ ≤ (1 - rLevel) * rLevel ^ (8 + i + 1) * ((z + 9) / 6 * (399 / 100)) := by
          gcongr
        _ = _ := by
          rw [hzv, show 8 + i + 1 = 9 + i by ring, pow_add]
          ring
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hG := arith_geom_sum_le L (a := 10 + 8 * Real.log 2) (b := Real.log 2)
      (by positivity) (by positivity)
    have hk : 0 ≤ (399 / 100) * (1 - rLevel) * rLevel ^ 9 / 6 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg hr0.le _)) (by norm_num)
    refine (mul_le_mul_of_nonneg_left hG hk).trans (le_of_eq ?_)
    have hinv : 1 / (1 - rLevel) = 2 + Real.sqrt 2 := by
      have hr : rLevel = Real.sqrt 2 / 2 := by
        unfold rLevel
        field_simp
        linarith
      rw [hr]
      have hne : 1 - Real.sqrt 2 / 2 ≠ 0 := by nlinarith
      rw [div_eq_iff hne]
      linear_combination (1 / 2) * hσ
    have hne : 1 - rLevel ≠ 0 := by linarith
    rw [hr9]
    have e2 : Real.log 2 / (1 - rLevel) ^ 2 = (Real.log 2 * (1 / (1 - rLevel))) / (1 - rLevel) := by
      field_simp
    rw [e2, hinv]
    field_simp
  have hval : (399 / 100) * (rLevel / 16) / 6 * ((10 + 8 * Real.log 2) + Real.log 2 * (2 + Real.sqrt 2)) ≤
      (399 / 100) * ((70711 / 100000) / 16) / 6 *
        ((10 + 8 * (6931471808 / 10000000000)) + (6931471808 / 10000000000) * (2 + 141422 / 100000)) := by
    have hru : rLevel ≤ 70711 / 100000 := by nlinarith
    have hA : (10 + 8 * Real.log 2) + Real.log 2 * (2 + Real.sqrt 2) ≤
        (10 + 8 * (6931471808 / 10000000000)) + (6931471808 / 10000000000) * (2 + 141422 / 100000) := by
      nlinarith [mul_le_mul hl1 (show 2 + Real.sqrt 2 ≤ 2 + 141422 / 100000 by linarith)
        (by positivity) (by norm_num)]
    have hA0 : 0 ≤ (10 + 8 * Real.log 2) + Real.log 2 * (2 + Real.sqrt 2) := by positivity
    have := mul_le_mul (show (399 / 100) * (rLevel / 16) / 6 ≤ (399 / 100) * ((70711 / 100000) / 16) / 6 by
      gcongr) hA hA0 (by norm_num)
    exact this
  have hrest' := hrest.trans hval
  norm_num at hfirst hrest' ⊢
  linarith

/-- The padded call cost of the survival-form bound. -/
theorem padded_levelSum_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2) (w : ℕ → ℝ)
    (hw : ∀ l ≤ L, w l ≤ 1 + ∑ k ∈ range l, cap k * survivalBound l k d) :
    ∑ l ∈ range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (26 / 5) * min (Real.sqrt (cap L)) d⁻¹ := by
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
    set C : ℕ → ℝ := fun j => if j = 0 then 89 / 20 else if j = 1 then 17 / 4 else 399 / 100 with hC
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
      · by_cases hj1 : j = 1
        · simp only [hC, ite_eq_right hj, ite_eq_left hj1]
          exact offset_le_rest s h1 h2 (by simp only [hv, hj1]; push_cast; nlinarith) I
        · simp only [hC, ite_eq_right hj, ite_eq_right hj1]
          have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
          exact offset_le_far s h1 h2 (by simp only [hv]; nlinarith) I
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
    have hconst := callCost_constant_le L
    have hconst' : ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) * (Real.sqrt (v j) * C j) ≤ 26 / 5 :=
      hconst
    have hdp : d * (∑ l ∈ range (L + 1), pLevel l * w l + rLevel ^ (L + 1)) ≤ 26 / 5 := by
      rw [hwsum] at hgridsum
      have hpd : d * ∑ l ∈ range (L + 1), pLevel l + d * rLevel ^ (L + 1) = d := by
        rw [← mul_add, hpsum, mul_one]
      have hx : d ≤ d * ((1 + Real.sqrt 2) * (rLevel * (1 - rLevel ^ L))) := by
        nlinarith
      nlinarith
    rw [← div_eq_mul_inv, le_div_iff₀ hd]
    linarith

/-- The padded call cost with the regime term. -/
theorem padded_regime_le (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2) (w : ℕ → ℝ)
    (hw : ∀ l ≤ L, w l ≤ 1 + ∑ k ∈ range l, cap k * survivalBound l k d) :
    ∑ l ∈ range (L + 1), pLevel l * w l + rLevel ^ (L + 1) ≤
      (26 / 5) * min (Real.sqrt (cap L)) d⁻¹ - (21 / 5) * UpperDisagreement.regimeTerm L d := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hp : ∀ l, 0 ≤ pLevel l := fun l => mul_nonneg (by linarith) (pow_nonneg hr0.le l)
  by_cases hreg : cap L * d ^ 2 ≤ 1
  · have hcapw : ∀ l ≤ L, w l ≤ cap l := by
      intro l hl
      refine (hw l hl).trans ?_
      have h : ∑ k ∈ range l, cap k * survivalBound l k d ≤ ∑ k ∈ range l, cap k :=
        sum_le_sum (fun k _ => mul_le_of_le_one_right (cap_pos k).le (survivalBound_le_one l k d))
      have hg : ∑ k ∈ range l, cap k = cap l - 1 := by
        change ∑ k ∈ range l, (2 : ℝ) ^ k = (2 : ℝ) ^ l - 1
        rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) l]
        norm_num
      linarith
    have h := sum_le_sum (fun l (hl : l ∈ range (L + 1)) => mul_le_mul_of_nonneg_left
      (hcapw l (Nat.le_of_lt_succ (mem_range.1 hl))) (hp l))
    rw [levelWeight_cap_sum, ← sqrt_cap] at h
    have hrL : rLevel ^ (L + 1) ≤ rLevel := by
      calc
        rLevel ^ (L + 1) ≤ rLevel ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
        _ = rLevel := pow_one _
    have hmin : min (Real.sqrt (cap L)) d⁻¹ = Real.sqrt (cap L) := by
      apply min_eq_left
      rw [← one_div, le_div_iff₀ hd, UpperDisagreement.sqrt_cap_mul L hd]
      exact Real.sqrt_le_one.mpr hreg
    have hreg' : UpperDisagreement.regimeTerm L d = Real.sqrt (cap L) := by unfold UpperDisagreement.regimeTerm; rw [ite_eq_left hreg]
    rw [hmin, hreg']
    linarith
  · have hreg' : UpperDisagreement.regimeTerm L d = 0 := by unfold UpperDisagreement.regimeTerm; rw [ite_eq_right hreg]
    rw [hreg', mul_zero, sub_zero]
    exact padded_levelSum_le L hd hdmax w hw

end ThresholdHC.UpperCallCost
