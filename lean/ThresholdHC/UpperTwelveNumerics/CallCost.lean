import ThresholdHC.UpperTwelveNumerics.Specification
import ThresholdHC.UpperCallCost.LevelSum

/-! The weighted sum of the call-cost offsets is below `5.19`.

The proof of `UpperCallCost.callCost_constant_le` bounds every partial sum of
`callCostTerm`, whose term `j` is `(1 - r)*r^(j+1)*sqrt v_{j+1}*C_{j+1}`, by a
rational certificate, about `5.18483`, and
then by `26/5`. The same certificate gives `5185/1000` (`callCost_partial_le`),
so the series converges and its sum is at most `5185/1000 < 519/100`. -/
noncomputable section
namespace ThresholdHC.UpperTwelveNumerics
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork ThresholdHC.UpperCost

theorem callCostTerm_nonneg (j : ℕ) : 0 ≤ callCostTerm j :=
  mul_nonneg (mul_nonneg (by linarith [rLevel_lt_one]) (pow_nonneg rLevel_pos.le _))
    (mul_nonneg (Real.sqrt_nonneg _) (UpperCallCost.callOffset_nonneg j))

/-- The partial sums, with the certificate of `UpperCallCost.callCost_constant_le`. -/
theorem callCost_sum_le (L : ℕ) :
    ∑ j ∈ range L, (1 - rLevel) * rLevel ^ (j + 1) *
      (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) *
        (if j = 0 then (89 / 20 : ℝ) else if j = 1 then 17 / 4 else 399 / 100)) ≤ 5185 / 1000 := by
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
    (mul_nonneg (Real.sqrt_nonneg _) (UpperCallCost.callOffset_nonneg j))
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
    have t0 := UpperCallCost.callTerm_le 0 (w := 20711 / 100000) (q := 130121 / 100000)
      (c := 89 / 20)
      (by have := UpperCallCost.weight_odd 0; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t1 := UpperCallCost.callTerm_le 1 (w := (2929 / 10000) * (1 / 2)) (q := 154477 / 100000)
      (c := 17 / 4)
      (by have := UpperCallCost.weight_even 0; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t2 := UpperCallCost.callTerm_le 2 (w := (20711 / 100000) * (1 / 2)) (q := 175484 / 100000)
      (c := 399 / 100)
      (by have := UpperCallCost.weight_odd 1; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t3 := UpperCallCost.callTerm_le 3 (w := (2929 / 10000) * (1 / 4)) (q := 194232 / 100000)
      (c := 399 / 100)
      (by have := UpperCallCost.weight_even 1; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t4 := UpperCallCost.callTerm_le 4 (w := (20711 / 100000) * (1 / 4)) (q := 211323 / 100000)
      (c := 399 / 100)
      (by have := UpperCallCost.weight_odd 2; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t5 := UpperCallCost.callTerm_le 5 (w := (2929 / 10000) * (1 / 8)) (q := 227132 / 100000)
      (c := 399 / 100)
      (by have := UpperCallCost.weight_even 2; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t6 := UpperCallCost.callTerm_le 6 (w := (20711 / 100000) * (1 / 8)) (q := 241910 / 100000)
      (c := 399 / 100)
      (by have := UpperCallCost.weight_odd 3; norm_num at this ⊢; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
    have t7 := UpperCallCost.callTerm_le 7 (w := (2929 / 10000) * (1 / 16)) (q := 255836 / 100000)
      (c := 399 / 100)
      (by have := UpperCallCost.weight_even 3; norm_num at this ⊢; linarith)
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
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg hr0.le _))
        (by norm_num)
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
  have hval : (399 / 100) * (rLevel / 16) / 6 *
        ((10 + 8 * Real.log 2) + Real.log 2 * (2 + Real.sqrt 2)) ≤
      (399 / 100) * ((70711 / 100000) / 16) / 6 *
        ((10 + 8 * (6931471808 / 10000000000)) +
          (6931471808 / 10000000000) * (2 + 141422 / 100000)) := by
    have hru : rLevel ≤ 70711 / 100000 := by nlinarith
    have hA : (10 + 8 * Real.log 2) + Real.log 2 * (2 + Real.sqrt 2) ≤
        (10 + 8 * (6931471808 / 10000000000)) +
          (6931471808 / 10000000000) * (2 + 141422 / 100000) := by
      nlinarith [mul_le_mul hl1 (show 2 + Real.sqrt 2 ≤ 2 + 141422 / 100000 by linarith)
        (by positivity) (by norm_num)]
    have hA0 : 0 ≤ (10 + 8 * Real.log 2) + Real.log 2 * (2 + Real.sqrt 2) := by positivity
    have := mul_le_mul (show (399 / 100) * (rLevel / 16) / 6 ≤
        (399 / 100) * ((70711 / 100000) / 16) / 6 by gcongr) hA hA0 (by norm_num)
    exact this
  have hrest' := hrest.trans hval
  norm_num at hfirst hrest' ⊢
  linarith

theorem callCost_partial_le (L : ℕ) : ∑ j ∈ range L, callCostTerm j ≤ 5185 / 1000 :=
  callCost_sum_le L

theorem callCost_summable : Summable callCostTerm :=
  summable_of_sum_range_le callCostTerm_nonneg callCost_partial_le

theorem callCost_tsum_le : ∑' j, callCostTerm j ≤ 5185 / 1000 :=
  Real.tsum_le_of_sum_range_le callCostTerm_nonneg callCost_partial_le

end ThresholdHC.UpperTwelveNumerics
