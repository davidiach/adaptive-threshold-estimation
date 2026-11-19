import ThresholdHC.UpperSign.Drift
import ThresholdHC.UpperSign.Offset

/-! The disagreement weights along the dyadic grid of levels.

The weight of level `l` is the cap part `exp(-2*x) + exp(-x)` from `x = 3/4` on,
one half plus the drift bounds of the smaller classifier below it, and one at
the first two levels (`signWeight`). Below the split, the drift bounds of the
level `i + 1` steps under the first grid point are at most `stepE i`
(`drift_step_le`). Weighted by `sqrt x`, the levels below the split add at most
`(1613/1000)*sqrt s`: the halves add up to `(1 + sqrt 2)/2` exactly, the first
two levels are covered by the halves of the geometric extension below them, and
the steps add at most the rest (`below_coef_le`). With the offset bound, the
weighted sum is at most `247/100` for every gap (`sign_grid_le`). -/
noncomputable section
namespace ThresholdHC.UpperSign
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2

section SignGrid
open Real Uniform713

/-- The weight of level `l` along the grid: the cap terms from `3/4` on, one half plus
the drift bounds of the smaller classifier below it, and one at the first two levels. -/
def signWeight (l : ℕ) (d : ℝ) : ℝ :=
  if 3 / 4 ≤ cap l * d ^ 2 then Real.exp (-2 * (cap l * d ^ 2)) + Real.exp (-(cap l * d ^ 2))
  else if 2 ≤ l then 1 / 2 + ∑ k ∈ range (l - 1), driftBound (l - 1) k d else 1

/-- The drift steps. -/
def stepE (i : ℕ) : ℝ :=
  if i = 0 then 56477 / 200000 else if i = 1 then 178521 / 1000000 else
    if i = 2 then 1253 / 10000 else if i = 3 then 19253 / 200000 else 79431 / 1000000

theorem stepE_nonneg (i : ℕ) : 0 ≤ stepE i := by
  unfold stepE
  split_ifs <;> norm_num

theorem driftBound_nonneg (L k : ℕ) (d : ℝ) : 0 ≤ driftBound L k d := by
  unfold driftBound
  split_ifs
  · exact (Real.exp_pos _).le
  · exact zero_le_one

/-- The drift bounds at the step of level difference `i`. -/
theorem drift_step_le (L : ℕ) {d : ℝ} (hd : 0 < d) (i : ℕ)
    (hx : cap L * d ^ 2 ≤ 3 / 2 ^ (i + 3)) :
    ∑ k ∈ range L, driftBound L k d ≤ stepE i := by
  unfold stepE
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · exact (driftSum_le L hd hx (by norm_num)).trans (by convert driftSeries_le_0 L using 3 <;> norm_num)
    · exact (driftSum_le L hd hx (by norm_num)).trans (by convert driftSeries_le_1 L using 3 <;> norm_num)
    · exact (driftSum_le L hd hx (by norm_num)).trans (by convert driftSeries_le_2 L using 3 <;> norm_num)
    · exact (driftSum_le L hd hx (by norm_num)).trans (by convert driftSeries_le_3 L using 3 <;> norm_num)
  · have h4 : cap L * d ^ 2 ≤ 3 / 2 ^ (4 + 3) := hx.trans (by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega))
    rw [ite_eq_right (show ¬ i = 0 by omega), ite_eq_right (show ¬ i = 1 by omega),
      ite_eq_right (show ¬ i = 2 by omega), ite_eq_right (show ¬ i = 3 by omega)]
    exact (driftSum_le L hd h4 (by norm_num)).trans (by convert driftSeries_le_4 L using 3; norm_num)

/-- The constant of the levels below the split. -/
theorem below_coef_le (n : ℕ) :
    ∑ i ∈ range n, rLevel ^ (i + 1) * (1 / 2 + stepE i) + rLevel ^ (n + 1) + rLevel ^ (n + 2) ≤
      1613 / 1000 := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hrσ : rLevel * Real.sqrt 2 = 1 := UpperWork.rLevel_mul_sqrt_two
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr2 : rLevel ^ 2 = 1 / 2 := by
    have : (rLevel * Real.sqrt 2) ^ 2 = 1 := by rw [hrσ]; norm_num
    rw [mul_pow, hσ] at this
    linarith
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hrl : (7071 / 10000 : ℝ) ≤ rLevel := by nlinarith
  have hru : rLevel ≤ 70711 / 100000 := by nlinarith
  -- the halves add up to `r + r^2` exactly
  have hhalf : ∀ n : ℕ, ∑ i ∈ range n, rLevel ^ (i + 1) * (1 / 2) + rLevel ^ (n + 1) +
      rLevel ^ (n + 2) = rLevel + rLevel ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      linear_combination ih + rLevel ^ (n + 1) * hr2
  -- the drift steps
  have hstep : ∑ i ∈ range n, rLevel ^ (i + 1) * stepE i ≤
      rLevel * (56477 / 200000) + rLevel ^ 2 * (178521 / 1000000) + rLevel ^ 3 * (1253 / 10000) +
        rLevel ^ 4 * (19253 / 200000) + (79431 / 1000000) * (rLevel ^ 5 * (2 + Real.sqrt 2)) := by
    have hext : ∑ i ∈ range n, rLevel ^ (i + 1) * stepE i ≤
        ∑ i ∈ range (4 + n), rLevel ^ (i + 1) * stepE i :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        (fun i _ _ => mul_nonneg (pow_nonneg hr0.le _) (stepE_nonneg i))
    rw [sum_range_add] at hext
    have h4 : ∑ i ∈ range 4, rLevel ^ (i + 1) * stepE i =
        rLevel * (56477 / 200000) + rLevel ^ 2 * (178521 / 1000000) + rLevel ^ 3 * (1253 / 10000) +
          rLevel ^ 4 * (19253 / 200000) := by
      simp [sum_range_succ, stepE]
    have htail : ∑ j ∈ range n, rLevel ^ (4 + j + 1) * stepE (4 + j) ≤
        (79431 / 1000000) * (rLevel ^ 5 * (2 + Real.sqrt 2)) := by
      have he : ∀ j, stepE (4 + j) = 79431 / 1000000 := by
        intro j
        unfold stepE
        rw [ite_eq_right (show ¬ 4 + j = 0 by omega), ite_eq_right (show ¬ 4 + j = 1 by omega),
          ite_eq_right (show ¬ 4 + j = 2 by omega), ite_eq_right (show ¬ 4 + j = 3 by omega)]
      simp only [he]
      have hg : ∑ j ∈ range n, rLevel ^ j ≤ 2 + Real.sqrt 2 := by
        have hs := sum_le_hasSum (range n) (fun j _ => pow_nonneg hr0.le j)
          (hasSum_geometric_of_lt_one hr0.le hr1)
        refine hs.trans (le_of_eq ?_)
        have hne : 1 - rLevel ≠ 0 := by linarith
        rw [eq_comm, ← mul_inv_cancel₀ hne]
        have h1r : (1 - rLevel) * (2 + Real.sqrt 2) = 1 := by
          linear_combination (-(1 + Real.sqrt 2)) * hrσ + rLevel * hσ
        field_simp
        linarith
      calc
        _ = (79431 / 1000000) * (rLevel ^ 5 * ∑ j ∈ range n, rLevel ^ j) := by
          rw [mul_sum, mul_sum]
          apply sum_congr rfl
          intro j _
          ring
        _ ≤ _ := by gcongr
    linarith
  have hr3 : rLevel ^ 3 = rLevel / 2 := by rw [pow_succ, hr2]; ring
  have hr4 : rLevel ^ 4 = 1 / 4 := by rw [show rLevel ^ 4 = (rLevel ^ 2) ^ 2 by ring, hr2]; norm_num
  have hr5 : rLevel ^ 5 = rLevel / 4 := by rw [pow_succ, hr4]; ring
  have hh := hhalf n
  have hsplit : ∑ i ∈ range n, rLevel ^ (i + 1) * (1 / 2 + stepE i) =
      ∑ i ∈ range n, rLevel ^ (i + 1) * (1 / 2) + ∑ i ∈ range n, rLevel ^ (i + 1) * stepE i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsplit]
  rw [hr3, hr4, hr5, hr2] at hstep
  nlinarith [mul_le_mul hru hσu (by linarith) (by linarith)]

end SignGrid

section SignGridSum
open Real Uniform713

theorem signWeight_nonneg (l : ℕ) (d : ℝ) : 0 ≤ signWeight l d := by
  unfold signWeight
  split_ifs
  · exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · exact add_nonneg (by norm_num) (sum_nonneg (fun k _ => driftBound_nonneg _ _ _))
  · exact zero_le_one

/-- The weights along the grid, for every gap. -/
theorem sign_grid_le {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2) (K : ℕ) :
    ∑ l ∈ range K, Real.sqrt (cap l * d ^ 2) * signWeight l d ≤ 247 / 100 := by
  classical
  set f : ℕ → ℝ := fun l => Real.sqrt (cap l * d ^ 2) * signWeight l d with hf
  have hf0 : ∀ l, 0 ≤ f l := fun l => mul_nonneg (Real.sqrt_nonneg _) (signWeight_nonneg _ _)
  have hdd : 0 < d ^ 2 := by positivity
  have hd4 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hex : ∃ l, 3 / 4 ≤ cap l * d ^ 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((3 / 4) / d ^ 2) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by have := (div_lt_iff₀ hdd).1 hn; simp only [cap]; linarith⟩
  set M := Nat.find hex with hM
  have hMspec : 3 / 4 ≤ cap M * d ^ 2 := Nat.find_spec hex
  have hMmin : ∀ l < M, cap l * d ^ 2 < 3 / 4 := fun l hl => not_le.1 (Nat.find_min hex hl)
  have hM2 : 2 ≤ M := by
    by_contra h
    have hle : cap M ≤ 2 := by
      have := Tier2.Model.cap_mono (show M ≤ 1 by omega)
      simpa [cap] using this
    nlinarith
  obtain ⟨n, hn⟩ : ∃ n, M = n + 2 := ⟨M - 2, by omega⟩
  set s := cap M * d ^ 2 with hs_def
  have hs2 : s ≤ 3 / 2 := by
    have h := hMmin (M - 1) (by omega)
    have hc : cap M = 2 * cap (M - 1) := by
      rw [show M = M - 1 + 1 by omega, cap_succ]
      simp
    rw [hs_def, hc]
    nlinarith
  have hext : ∑ l ∈ range K, f l ≤ ∑ l ∈ range (M + K), f l :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun l _ _ => hf0 l)
  rw [sum_range_add] at hext
  -- above the split
  have hpost : ∀ i, f (M + i) = UpperDisagreement.capTerm (2 ^ i * s) := by
    intro i
    have hcap : cap (M + i) * d ^ 2 = 2 ^ i * s := by
      rw [hs_def, show cap (M + i) = 2 ^ i * cap M by simp only [cap]; ring]
      ring
    have hge : 3 / 4 ≤ cap (M + i) * d ^ 2 := by
      rw [hcap]
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    simp only [hf, signWeight, UpperDisagreement.capTerm]
    rw [ite_eq_left hge, hcap]
  rw [sum_congr rfl (fun i _ => hpost i)] at hext
  -- below the split
  have hroot : ∀ i, i < M → Real.sqrt (cap (M - 1 - i) * d ^ 2) =
      Real.sqrt s * rLevel ^ (i + 1) := by
    intro i hi
    have hc : cap M = cap (M - 1 - i) * 2 ^ (i + 1) := by
      rw [show M = (M - 1 - i) + (i + 1) by omega]
      simp only [cap, pow_add]
      rw [show M - 1 - i + (i + 1) - 1 - i = M - 1 - i by omega]
    have hsx : cap (M - 1 - i) * d ^ 2 = s * (rLevel ^ (i + 1)) ^ 2 := by
      have hr2 : rLevel ^ 2 = 1 / 2 := by
        have h := UpperWork.rLevel_mul_sqrt_two
        have : (rLevel * Real.sqrt 2) ^ 2 = 1 := by rw [h]; norm_num
        rw [mul_pow, Real.sq_sqrt (by norm_num)] at this
        linarith
      rw [← pow_mul, mul_comm (i + 1) 2, pow_mul, hr2, hs_def, hc]
      rw [mul_assoc, mul_assoc, show (2 : ℝ) ^ (i + 1) * (d ^ 2 * (1 / 2) ^ (i + 1)) =
        d ^ 2 * ((2 : ℝ) ^ (i + 1) * (1 / 2) ^ (i + 1)) by ring, ← mul_pow]
      norm_num
    rw [hsx, Real.sqrt_mul (by positivity), Real.sqrt_sq (pow_nonneg rLevel_pos.le _)]
  have hbelow : ∑ l ∈ range M, f l ≤ (1613 / 1000) * Real.sqrt s := by
    rw [← sum_range_reflect f M]
    have hterm : ∀ i ∈ range n, f (M - 1 - i) ≤
        Real.sqrt s * (rLevel ^ (i + 1) * (1 / 2 + stepE i)) := by
      intro i hi
      have hi' := mem_range.1 hi
      have hl2 : 2 ≤ M - 1 - i := by omega
      have hlt : cap (M - 1 - i) * d ^ 2 < 3 / 4 := hMmin _ (by omega)
      have hdrift : ∑ k ∈ range (M - 1 - i - 1), driftBound (M - 1 - i - 1) k d ≤ stepE i := by
        apply drift_step_le _ hd
        have hc : cap M = cap (M - 1 - i - 1) * 2 ^ (i + 2) := by
          rw [show M = (M - 1 - i - 1) + (i + 2) by omega]
          simp only [cap, pow_add]
          rw [show M - 1 - i - 1 + (i + 2) - 1 - i - 1 = M - 1 - i - 1 by omega]
        have : cap (M - 1 - i - 1) * d ^ 2 * 2 ^ (i + 2) = s := by rw [hs_def, hc]; ring
        rw [le_div_iff₀ (by positivity)]
        have h2 : (2 : ℝ) ^ (i + 3) = 2 * 2 ^ (i + 2) := by ring
        rw [h2]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (i + 2)]
      simp only [hf, signWeight]
      rw [ite_eq_right (not_le.2 hlt), ite_eq_left hl2, hroot i (by omega)]
      have hs0 : 0 ≤ Real.sqrt s * rLevel ^ (i + 1) :=
        mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg rLevel_pos.le _)
      calc
        _ ≤ Real.sqrt s * rLevel ^ (i + 1) * (1 / 2 + stepE i) := by gcongr
        _ = _ := by ring
    have h1 : f (M - 1 - n) ≤ Real.sqrt s * rLevel ^ (n + 1) := by
      have hl : M - 1 - n = 1 := by omega
      have hlt : cap 1 * d ^ 2 < 3 / 4 := hMmin 1 (by omega)
      simp only [hf]
      rw [hroot n (by omega)]
      rw [hl]
      simp only [signWeight]
      rw [ite_eq_right (not_le.2 hlt), ite_eq_right (by norm_num), mul_one]
    have h0 : f (M - 1 - (n + 1)) ≤ Real.sqrt s * rLevel ^ (n + 2) := by
      have hl : M - 1 - (n + 1) = 0 := by omega
      have hlt : cap 0 * d ^ 2 < 3 / 4 := hMmin 0 (by omega)
      simp only [hf]
      rw [hroot (n + 1) (by omega)]
      rw [hl]
      simp only [signWeight]
      rw [ite_eq_right (not_le.2 hlt), ite_eq_right (by norm_num), mul_one]
    rw [hn, sum_range_succ, sum_range_succ]
    rw [← hn]
    have hS := sum_le_sum hterm
    rw [← mul_sum] at hS
    have hc := below_coef_le n
    have hs0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    nlinarith [mul_le_mul_of_nonneg_left hc hs0]
  have hb := sign_offset_le s hMspec hs2 K
  linarith

end SignGridSum

end ThresholdHC.UpperSign
