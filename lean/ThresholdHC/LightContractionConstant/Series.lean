import ThresholdHC.LightContractionConstant.Masses

/-! The series `C_V`. Each summand is nonnegative. The `k = 2` summand is at
most `64(1 + log 2) < 128`, since `p log(1/p) ≤ 1 - p`. For `k ≥ 3` the map
`p ↦ p(1 + log(1/p) + log 2)` is increasing on `[0,2]`, so the summand is at
most its value at `2e^{-4^k/2}`, and the inequality `e^x ≥ x^4/24` (through
`light_exponential_cost`) bounds it by `12·16^{-n}`, `k = n+2`. Hence every
summand is at most `192·16^{-j}`, `k = j+2`, the series converges and
`C_V ≤ 1024/5 < 256`. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.LightContractionConstant
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.ArbitraryLawAdaptation

theorem log_one_div_nonneg_of_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ log (1/p) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  · exact log_nonneg ((le_div_iff₀ hp).mpr (by linarith))

theorem mul_log_one_div_le {p : ℝ} (hp : 0 ≤ p) : p * log (1/p) ≤ 1 - p := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  · have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (one_div_pos.mpr hp)) hp.le
    calc p * log (1/p) ≤ p * (1/p - 1) := h
      _ = 1 - p := by field_simp

/-- The map `p ↦ p(1 + log(1/p) + log 2)` is monotone on `[0,2]`. -/
theorem bracket_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2) :
    p * (1 + log (1/p) + log 2) ≤ q * (1 + log (1/q) + log 2) := by
  rcases hp.eq_or_lt with rfl | hp
  · rw [zero_mul]
    rcases hpq.eq_or_lt with rfl | hq0
    · simp
    · have h2 : log q ≤ log 2 := log_le_log hq0 hq
      rw [one_div, log_inv]
      exact mul_nonneg hq0.le (by linarith)
  · have hq0 : 0 < q := lt_of_lt_of_le hp hpq
    have h1 := log_le_sub_one_of_pos (div_pos hq0 hp)
    rw [log_div hq0.ne' hp.ne'] at h1
    have h1' : p * (log q - log p) ≤ q - p := by
      calc p * (log q - log p) ≤ p * (q/p - 1) := mul_le_mul_of_nonneg_left h1 hp.le
        _ = q - p := by field_simp
    have h2 : log q ≤ log 2 := log_le_log hq0 hq
    rw [one_div, log_inv, one_div, log_inv]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr h2)]

theorem cvTerm_nonneg (ν : Measure Gap) [IsProbabilityMeasure ν] (k : ℕ) :
    0 ≤ cvTerm ν k := by
  have h0 := bandProb_nonneg ν k
  have hl := log_one_div_nonneg_of_le_one h0 (bandProb_le_one ν k)
  have h2 : 0 ≤ log 2 := log_nonneg one_le_two
  unfold cvTerm
  exact mul_nonneg (mul_nonneg (by positivity) h0) (by linarith)

theorem cvTerm_first_le (ν : Measure Gap) [IsProbabilityMeasure ν] :
    cvTerm ν 2 ≤ 64 * (1 + log 2) := by
  have h0 := bandProb_nonneg ν 2
  have h1 := bandProb_le_one ν 2
  have hl := mul_log_one_div_le h0
  have h2 : 0 ≤ log 2 := log_nonneg one_le_two
  have h3 : bandProb ν 2 * log 2 ≤ log 2 := mul_le_of_le_one_left h2 h1
  calc cvTerm ν 2 = 64 * (bandProb ν 2 + bandProb ν 2 * log (1 / bandProb ν 2) +
        bandProb ν 2 * log 2) := by unfold cvTerm; norm_num; ring
    _ ≤ 64 * (1 + log 2) := by linarith

theorem cvTerm_first_lt (ν : Measure Gap) [IsProbabilityMeasure ν] : cvTerm ν 2 < 192 := by
  have h := cvTerm_first_le ν
  have h2 : log 2 < 1 := by linarith [log_two_lt_d9]
  linarith

/-- The real tail estimate behind the summands with `k = n+2 ≥ 3`. -/
theorem tail_bracket_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hpq : p ≤ 2 * exp (-((4 : ℝ)^(n+2) / 2))) :
    (4 : ℝ)^(n+3) * (p * (1 + log (1/p) + log 2)) ≤ 12 * (1/16 : ℝ)^n := by
  have hx : (16 : ℝ) ≤ (4 : ℝ)^(n+2) := by
    calc (16 : ℝ) = 4^2 := by norm_num
      _ ≤ 4^(n+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : exp (-((4 : ℝ)^(n+2) / 2)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hq2 : 2 * exp (-((4 : ℝ)^(n+2) / 2)) ≤ 2 := by linarith
  have hlog : log (1 / (2 * exp (-((4 : ℝ)^(n+2) / 2)))) = (4 : ℝ)^(n+2) / 2 - log 2 := by
    rw [one_div, log_inv, log_mul two_ne_zero (exp_pos _).ne', log_exp]
    ring
  have hmono := bracket_mono hp0 hpq hq2
  rw [hlog] at hmono
  have hcost := light_exponential_cost n
  have hq0 : 0 ≤ 2 * exp (-((4 : ℝ)^(n+2) / 2)) := by positivity
  have hb : 1 + ((4 : ℝ)^(n+2) / 2 - log 2) + log 2 ≤ (4 : ℝ)^(n+2) := by linarith
  calc (4 : ℝ)^(n+3) * (p * (1 + log (1/p) + log 2))
      ≤ (4 : ℝ)^(n+3) * (2 * exp (-((4 : ℝ)^(n+2) / 2)) *
          (1 + ((4 : ℝ)^(n+2) / 2 - log 2) + log 2)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ (4 : ℝ)^(n+3) * (2 * exp (-((4 : ℝ)^(n+2) / 2)) * (4 : ℝ)^(n+2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hq0) (by positivity)
    _ = (4 : ℝ)^(n+1) * ((4 : ℝ)^(n+4) * (2 * exp (-((4 : ℝ)^(n+2) / 2)))) := by ring
    _ ≤ (4 : ℝ)^(n+1) * (3 * (1/64 : ℝ)^n) := mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = 12 * (1/16 : ℝ)^n := by
        rw [show (1/16 : ℝ) = 4 * (1/64) by norm_num, mul_pow]
        ring

theorem cvTerm_tail_le (ν : Measure Gap)
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x))
    (n : ℕ) (hn : 1 ≤ n) : cvTerm ν (n+2) ≤ 12 * (1/16 : ℝ)^n := by
  have h := tail_bracket_le n (bandProb_nonneg ν (n+2)) (bandProb_tail ν hCDF n hn)
  calc cvTerm ν (n+2) = (4 : ℝ)^(n+3) * (bandProb ν (n+2) *
        (1 + log (1 / bandProb ν (n+2)) + log 2)) := by unfold cvTerm; ring
    _ ≤ _ := h

/-- Every summand is at most `192·16^{-j}`, `k = j+2`. -/
theorem cvTerm_le_geometric (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) (j : ℕ) :
    cvTerm ν (j+2) ≤ 192 * (1/16 : ℝ)^j := by
  cases j with
  | zero =>
    have h := cvTerm_first_le ν
    have h2 : log 2 < 1 := by linarith [log_two_lt_d9]
    simp only [zero_add, pow_zero, mul_one]
    linarith
  | succ n =>
    have h := cvTerm_tail_le ν hCDF (n+1) (by omega)
    have hp : (0 : ℝ) ≤ (1/16 : ℝ)^(n+1) := by positivity
    linarith

theorem geometric_summable : Summable (fun j : ℕ => 192 * (1/16 : ℝ)^j) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 192

theorem cvTerm_summable (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    Summable (fun j : ℕ => cvTerm ν (j+2)) :=
  Summable.of_nonneg_of_le (fun j => cvTerm_nonneg ν (j+2)) (cvTerm_le_geometric ν hCDF)
    geometric_summable

theorem lightCV_le (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    lightCV ν ≤ 1024/5 := by
  unfold lightCV
  calc ∑' j : ℕ, cvTerm ν (j+2) ≤ ∑' j : ℕ, 192 * (1/16 : ℝ)^j :=
        Summable.tsum_le_tsum (cvTerm_le_geometric ν hCDF) (cvTerm_summable ν hCDF)
          geometric_summable
    _ = 192 * (1 - 1/16)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 1024/5 := by norm_num

theorem lightCV_lt (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    lightCV ν < 256 :=
  (lightCV_le ν hCDF).trans_lt (by norm_num)

end ThresholdHC.LightContractionConstant
