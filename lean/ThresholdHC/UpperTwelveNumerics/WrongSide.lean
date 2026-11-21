import ThresholdHC.UpperTwelveNumerics.Specification

/-! The wrong-side early stops: the constant is below `0.401`.

`UpperDisagreement.stopError_sum_le` bounds the early-stopping parts of the
larger classifier, summed with the weights `1/p_l` and multiplied by `d`, by
`(2+sqrt 2)^2/(4*13/10)*e^{-2}*sqrt 2/(4-sqrt 2)`. The parts of the smaller
classifier add at most `sqrt 2` times as much, since `1/p_l = sqrt 2/p_{l-1}`,
which gives `wrongSideConstant` (`wrongSide_levelSum_le`). With
`e^{-2} ≤ 13533529/10^8`, from `e > 2.7182818283`, and `sqrt 2 ≤ 1.41422`, the
constant is below `401/1000` (`wrongSideConstant_lt`). The existing bound
`e^{-2} ≤ 339/2500` would give about `0.4014`. -/
noncomputable section
namespace ThresholdHC.UpperTwelveNumerics
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- `e^{-2} ≤ 0.13533529`. -/
theorem exp_neg_two_le_fine : Real.exp (-2) ≤ 13533529 / 100000000 := by
  have h1 := Real.exp_one_gt_d9
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hprod : Real.exp (-2) * (Real.exp 1 * Real.exp 1) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have ha : (27182818283 / 10000000000 : ℝ) * (27182818283 / 10000000000) ≤
      Real.exp 1 * Real.exp 1 := by
    have h1' : (27182818283 / 10000000000 : ℝ) ≤ Real.exp 1 := by
      have := h1
      norm_num at this ⊢
      linarith
    exact mul_le_mul h1' h1' (by norm_num) he1.le
  have hE := (Real.exp_pos (-2)).le
  have hb : Real.exp (-2) * ((27182818283 / 10000000000 : ℝ) * (27182818283 / 10000000000)) ≤ 1 := by
    calc
      _ ≤ Real.exp (-2) * (Real.exp 1 * Real.exp 1) := mul_le_mul_of_nonneg_left ha hE
      _ = 1 := hprod
  norm_num at hb
  linarith

theorem wrongSideConstant_lt : wrongSideConstant < 401 / 1000 := by
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have he := exp_neg_two_le_fine
  have hq : Real.sqrt 2 / (4 - Real.sqrt 2) ≤ 141422 / 258578 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hq0 : 0 ≤ Real.sqrt 2 / (4 - Real.sqrt 2) := div_nonneg (by positivity) (by linarith)
  have hA : (1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10))) ≤
      (1 + 141422 / 100000) * ((2 + 141422 / 100000) ^ 2 / (4 * (13 / 10))) := by
    gcongr
  have hA0 : 0 ≤ (1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10))) := by positivity
  have he0 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  unfold wrongSideConstant
  calc
    _ = ((1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10)))) * Real.exp (-2) *
        (Real.sqrt 2 / (4 - Real.sqrt 2)) := by ring
    _ ≤ ((1 + 141422 / 100000) * ((2 + 141422 / 100000) ^ 2 / (4 * (13 / 10)))) *
        (13533529 / 100000000) * (141422 / 258578) := by gcongr
    _ < 401 / 1000 := by norm_num

/-- Both consecutive classifiers: at most `wrongSideConstant` divided by `d`. -/
theorem wrongSide_levelSum_le (L : ℕ) {d : ℝ} (hd : 0 < d) :
    d * ∑ l ∈ range (L + 1),
        (UpperDisagreement.stopError l d + UpperDisagreement.stopError (l - 1) d) / pLevel l ≤
      wrongSideConstant := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hrσ : rLevel * Real.sqrt 2 = 1 := UpperWork.rLevel_mul_sqrt_two
  have hp : ∀ l, 0 < pLevel l := fun l => mul_pos (by linarith) (pow_pos hr0 l)
  -- the level `l - 1` parts are `sqrt 2` times the level parts
  have hshift : ∑ l ∈ range (L + 1), UpperDisagreement.stopError (l - 1) d / pLevel l ≤
      Real.sqrt 2 * ∑ l ∈ range (L + 1), UpperDisagreement.stopError l d / pLevel l := by
    rw [sum_range_succ']
    simp only [Nat.zero_sub, Nat.add_sub_cancel]
    have h0 : UpperDisagreement.stopError 0 d = 0 := by simp [UpperDisagreement.stopError]
    rw [h0, zero_div, add_zero, mul_sum]
    have hle : ∑ i ∈ range L, UpperDisagreement.stopError i d / pLevel (i + 1) ≤
        ∑ i ∈ range (L + 1), Real.sqrt 2 * (UpperDisagreement.stopError i d / pLevel i) := by
      have hterm : ∀ i ∈ range L, UpperDisagreement.stopError i d / pLevel (i + 1) =
          Real.sqrt 2 * (UpperDisagreement.stopError i d / pLevel i) := by
        intro i _
        rw [show pLevel (i + 1) = pLevel i * rLevel by unfold pLevel; ring, ← div_div,
          div_eq_mul_inv (UpperDisagreement.stopError i d / pLevel i),
          inv_eq_of_mul_eq_one_right hrσ]
        ring
      rw [sum_congr rfl hterm]
      exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ =>
        mul_nonneg (Real.sqrt_nonneg 2)
          (div_nonneg (UpperDisagreement.stopError_nonneg i d) (hp i).le))
    exact hle
  have hmain := UpperDisagreement.stopError_sum_le L hd
  have hsplit : ∑ l ∈ range (L + 1),
        (UpperDisagreement.stopError l d + UpperDisagreement.stopError (l - 1) d) / pLevel l =
      ∑ l ∈ range (L + 1), UpperDisagreement.stopError l d / pLevel l +
        ∑ l ∈ range (L + 1), UpperDisagreement.stopError (l - 1) d / pLevel l := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro l _
    rw [add_div]
  rw [hsplit]
  set T := ∑ l ∈ range (L + 1), UpperDisagreement.stopError l d / pLevel l with hT
  set T' := ∑ l ∈ range (L + 1), UpperDisagreement.stopError (l - 1) d / pLevel l with hT'
  have hd0 := hd.le
  have h1 : d * T' ≤ Real.sqrt 2 * (d * T) := by
    calc
      d * T' ≤ d * (Real.sqrt 2 * T) := mul_le_mul_of_nonneg_left hshift hd0
      _ = Real.sqrt 2 * (d * T) := by ring
  have h2 : (1 + Real.sqrt 2) * (d * T) ≤
      (1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10)) * Real.exp (-2) *
        (Real.sqrt 2 / (4 - Real.sqrt 2))) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  unfold wrongSideConstant
  calc
    d * (T + T') = d * T + d * T' := by ring
    _ ≤ d * T + Real.sqrt 2 * (d * T) := by linarith
    _ = (1 + Real.sqrt 2) * (d * T) := by ring
    _ ≤ _ := h2

end ThresholdHC.UpperTwelveNumerics
