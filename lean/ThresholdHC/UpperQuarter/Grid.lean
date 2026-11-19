import ThresholdHC.UpperQuarter.DriftTable
import ThresholdHC.UpperQuarter.Offset
import ThresholdHC.UpperSign.Grid

/-! The weights of the levels along the dyadic grid, with the vote-change bound.

At scale `x = cap l*d^2`, level `l` carries the weight `quarterWeight l d`: the
cap terms `exp(-2*x) + exp(-x)` from the split `19/20` on; below it, one quarter
plus the drift bounds of the smaller classifier for `l ≥ 1`; and one at the
first level. The first grid point `s` at or above the split lies in
`[19/20, 19/10]`, which is cut into four bands. In band `k`, the drift bounds of
the `(i+1)`-th level below `s` are at most the tabulated `bandStep k i`, the
levels below the split add at most `bandCoef k*sqrt s` (`below_quarter_le`), and
the offset lemmas bound the total by `89/50` (`quarter_grid_le`). -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2 ThresholdHC.UpperSign

section QuarterWeight
open Real Uniform713

/-- The weight of level `l` along the grid, with the split at `19/20`. -/
def quarterWeight (l : ℕ) (d : ℝ) : ℝ :=
  if 19 / 20 ≤ cap l * d ^ 2 then Real.exp (-2 * (cap l * d ^ 2)) + Real.exp (-(cap l * d ^ 2))
  else if 1 ≤ l then 1 / 4 + ∑ k ∈ range (l - 1), driftBound (l - 1) k d else 1

theorem quarterWeight_nonneg (l : ℕ) (d : ℝ) : 0 ≤ quarterWeight l d := by
  unfold quarterWeight
  split_ifs
  · exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · exact add_nonneg (by norm_num) (sum_nonneg (fun k _ => driftBound_nonneg _ _ _))
  · exact zero_le_one

/-- The lower ends of the four bands. -/
def bandBot (k : ℕ) : ℝ :=
  if k = 0 then 19 / 20 else if k = 1 then 19 / 16 else if k = 2 then 57 / 40 else 133 / 80

/-- The upper ends of the four bands. -/
def bandTop (k : ℕ) : ℝ :=
  if k = 0 then 19 / 16 else if k = 1 then 57 / 40 else if k = 2 then 133 / 80 else 19 / 10

/-- The coefficients of the levels below the split, by band. -/
def bandCoef (k : ℕ) : ℝ :=
  if k = 0 then 24 / 25 else if k = 1 then 997 / 1000 else if k = 2 then 207 / 200 else 1073 / 1000

/-- The tabulated drift steps, by band and level difference. -/
def bandStep (k i : ℕ) : ℝ :=
  if k = 0 then
    (if i = 0 then 29883 / 125000 else if i = 1 then 3917 / 25000 else if i = 2 then 113601 / 1000000
      else if i = 3 then 44797 / 500000 else 75413 / 1000000)
  else if k = 1 then
    (if i = 0 then 271967 / 1000000 else if i = 1 then 21663 / 125000 else if i = 2 then 3829 / 31250
      else if i = 3 then 18939 / 200000 else 78491 / 1000000)
  else if k = 2 then
    (if i = 0 then 19063 / 62500 else if i = 1 then 189799 / 1000000 else if i = 2 then 131249 / 1000000
      else if i = 3 then 12451 / 125000 else 81419 / 1000000)
  else
    (if i = 0 then 67639 / 200000 else if i = 1 then 206233 / 1000000 else if i = 2 then 139823 / 1000000
      else if i = 3 then 104379 / 1000000 else 84231 / 1000000)

end QuarterWeight

section QuarterSteps
open Real Uniform713

theorem bandStep_tail (k i : ℕ) (hi : 4 ≤ i) : bandStep k i = bandStep k 4 := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  have h3 : i ≠ 3 := by omega
  unfold bandStep
  simp [h0, h1, h2, h3]

/-- The drift bounds of a classifier whose scale is at most `bandTop k/2^(i+2)` are at most
the tabulated step. -/
theorem band_step_le (k : ℕ) (hk : k < 4) (L i : ℕ) {d : ℝ} (hd : 0 < d)
    (hx : cap L * d ^ 2 ≤ bandTop k / 2 ^ (i + 2)) :
    ∑ j ∈ range L, driftBound L j d ≤ bandStep k i := by
  have key : ∀ Y e : ℝ, cap L * d ^ 2 ≤ Y → Y ≤ 1 / 2 →
      (∑ J ∈ range L, driftTerm (J + 1) Y ≤ e) → ∑ j ∈ range L, driftBound L j d ≤ e :=
    fun Y e hxY hY h => (driftSum_le_half L hd hxY hY).trans h
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases k <;> interval_cases i <;> simp only [bandTop, bandStep] at hx ⊢ <;> norm_num at hx ⊢
    · exact key (19 / 64) _ hx (by norm_num) (quarterSeries_le_0_0 L)
    · exact key (19 / 128) _ hx (by norm_num) (quarterSeries_le_0_1 L)
    · exact key (19 / 256) _ hx (by norm_num) (quarterSeries_le_0_2 L)
    · exact key (19 / 512) _ hx (by norm_num) (quarterSeries_le_0_3 L)
    · exact key (57 / 160) _ hx (by norm_num) (quarterSeries_le_1_0 L)
    · exact key (57 / 320) _ hx (by norm_num) (quarterSeries_le_1_1 L)
    · exact key (57 / 640) _ hx (by norm_num) (quarterSeries_le_1_2 L)
    · exact key (57 / 1280) _ hx (by norm_num) (quarterSeries_le_1_3 L)
    · exact key (133 / 320) _ hx (by norm_num) (quarterSeries_le_2_0 L)
    · exact key (133 / 640) _ hx (by norm_num) (quarterSeries_le_2_1 L)
    · exact key (133 / 1280) _ hx (by norm_num) (quarterSeries_le_2_2 L)
    · exact key (133 / 2560) _ hx (by norm_num) (quarterSeries_le_2_3 L)
    · exact key (19 / 40) _ hx (by norm_num) (quarterSeries_le_3_0 L)
    · exact key (19 / 80) _ hx (by norm_num) (quarterSeries_le_3_1 L)
    · exact key (19 / 160) _ hx (by norm_num) (quarterSeries_le_3_2 L)
    · exact key (19 / 320) _ hx (by norm_num) (quarterSeries_le_3_3 L)
  · rw [bandStep_tail k i hi]
    have hdec : bandTop k / 2 ^ (i + 2) ≤ bandTop k / 2 ^ (4 + 2) := by
      have ht : 0 ≤ bandTop k := by unfold bandTop; split_ifs <;> norm_num
      exact div_le_div_of_nonneg_left ht (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    have hx4 := hx.trans hdec
    interval_cases k <;> simp only [bandTop, bandStep] at hx4 ⊢ <;> norm_num at hx4 ⊢
    · exact key (19 / 1024) _ hx4 (by norm_num) (quarterSeries_le_0_4 L)
    · exact key (57 / 2560) _ hx4 (by norm_num) (quarterSeries_le_1_4 L)
    · exact key (133 / 5120) _ hx4 (by norm_num) (quarterSeries_le_2_4 L)
    · exact key (19 / 640) _ hx4 (by norm_num) (quarterSeries_le_3_4 L)

/-- The levels below the split, with step bounds `e` that are constant from the fifth on:
`n` levels with weight one quarter plus the step, and the first level with weight one. -/
theorem below_quarter_le (e : ℕ → ℝ) (E4 : ℝ) (he4 : ∀ i, 4 ≤ i → e i = E4)
    (hmono : ∀ i, 3 / 4 - rLevel ≤ e i) (n : ℕ) :
    ∑ i ∈ range n, rLevel ^ (i + 1) * (1 / 4 + e i) + rLevel ^ (n + 1) ≤
      ∑ i ∈ range 4, rLevel ^ (i + 1) * (1 / 4 + e i) +
        rLevel ^ 5 * ((1 / 4 + E4) * (2 + Real.sqrt 2)) := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hrσ : rLevel * Real.sqrt 2 = 1 := UpperWork.rLevel_mul_sqrt_two
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1r : (1 - rLevel) * (2 + Real.sqrt 2) = 1 := by
    linear_combination (-(1 + Real.sqrt 2)) * hrσ + rLevel * hσ
  set T : ℕ → ℝ := fun n => ∑ i ∈ range n, rLevel ^ (i + 1) * (1 / 4 + e i) + rLevel ^ (n + 1)
    with hT
  have hstep : ∀ n, T n ≤ T (n + 1) := by
    intro n
    simp only [hT, sum_range_succ]
    have h := mul_nonneg (pow_nonneg hr0.le (n + 1)) (show 0 ≤ e n - (3 / 4 - rLevel) by
      linarith [hmono n])
    have hp : rLevel ^ (n + 1 + 1) = rLevel ^ (n + 1) * rLevel := pow_succ _ _
    nlinarith
  have hmon : ∀ m, T n ≤ T (n + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => exact ih.trans (hstep (n + m))
  set c : ℝ := 1 / 4 + E4 with hc
  have hc1 : 1 ≤ c * (2 + Real.sqrt 2) := by
    have h4 := hmono 4
    rw [he4 4 le_rfl] at h4
    nlinarith [Real.sqrt_nonneg 2]
  have hid : ∀ m : ℕ, ∑ j ∈ range m, rLevel ^ j * c + rLevel ^ m * (c * (2 + Real.sqrt 2)) =
      c * (2 + Real.sqrt 2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      linear_combination ih - rLevel ^ m * c * h1r
  have h4 : T (n + 4) ≤ ∑ i ∈ range 4, rLevel ^ (i + 1) * (1 / 4 + e i) +
      rLevel ^ 5 * ((1 / 4 + E4) * (2 + Real.sqrt 2)) := by
    simp only [hT]
    rw [show n + 4 = 4 + n by ring, sum_range_add]
    have hsum : ∑ j ∈ range n, rLevel ^ (4 + j + 1) * (1 / 4 + e (4 + j)) =
        rLevel ^ 5 * ∑ j ∈ range n, rLevel ^ j * c := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [he4 (4 + j) (by omega), ← hc]
      ring
    rw [hsum]
    have hm := hid n
    have hpow : rLevel ^ (4 + n + 1) = rLevel ^ 5 * rLevel ^ n := by ring
    rw [hpow]
    have hr5 : 0 ≤ rLevel ^ 5 := pow_nonneg hr0.le 5
    have hrn : 0 ≤ rLevel ^ n := pow_nonneg hr0.le n
    have hkey : ∑ j ∈ range n, rLevel ^ j * c + rLevel ^ n ≤ c * (2 + Real.sqrt 2) := by
      nlinarith
    have hfin := mul_le_mul_of_nonneg_left hkey hr5
    rw [mul_add] at hfin
    rw [← hc]
    linarith
  exact (hmon 4).trans h4

/-- The coefficient of the levels below the split, by band. -/
theorem band_coef_le (k : ℕ) (hk : k < 4) (n : ℕ) :
    ∑ i ∈ range n, rLevel ^ (i + 1) * (1 / 4 + bandStep k i) + rLevel ^ (n + 1) ≤ bandCoef k := by
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hrσ : rLevel * Real.sqrt 2 = 1 := UpperWork.rLevel_mul_sqrt_two
  have hr0 := rLevel_pos
  have hrl : (7071 / 10000 : ℝ) ≤ rLevel := by nlinarith
  have hru : rLevel ≤ 70711 / 100000 := by nlinarith
  have hr2 : rLevel ^ 2 = 1 / 2 := by
    have : (rLevel * Real.sqrt 2) ^ 2 = 1 := by rw [hrσ]; norm_num
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at this
    linarith
  have hmono : ∀ i, 3 / 4 - rLevel ≤ bandStep k i := by
    intro i
    have h : (7 / 100 : ℝ) ≤ bandStep k i := by
      unfold bandStep; split_ifs <;> norm_num
    linarith
  refine (below_quarter_le (bandStep k) (bandStep k 4) (fun i hi => bandStep_tail k i hi) hmono n).trans ?_
  have hr3 : rLevel ^ 3 = rLevel / 2 := by rw [pow_succ, hr2]; ring
  have hr4 : rLevel ^ 4 = 1 / 4 := by rw [show rLevel ^ 4 = (rLevel ^ 2) ^ 2 by ring, hr2]; norm_num
  have hr5 : rLevel ^ 5 = rLevel / 4 := by rw [pow_succ, hr4]; ring
  have hr5σ : rLevel ^ 5 * (2 + Real.sqrt 2) = rLevel / 2 + 1 / 4 := by
    rw [hr5]; linear_combination (1 / 4) * hrσ
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [show rLevel ^ (0 + 1) = rLevel by ring, show rLevel ^ (1 + 1) = rLevel ^ 2 by ring,
    show rLevel ^ (2 + 1) = rLevel ^ 3 by ring, show rLevel ^ (3 + 1) = rLevel ^ 4 by ring, hr2, hr3, hr4,
    show rLevel ^ 5 * ((1 / 4 + bandStep k 4) * (2 + Real.sqrt 2)) =
      (1 / 4 + bandStep k 4) * (rLevel ^ 5 * (2 + Real.sqrt 2)) by ring, hr5σ]
  interval_cases k <;> simp only [bandStep, bandCoef] <;> norm_num <;> nlinarith

/-- The offset sum of the band. -/
theorem band_offset_le (k : ℕ) (hk : k < 4) (s : ℝ) (h1 : bandBot k ≤ s) (h2 : s ≤ bandTop k) (I : ℕ) :
    bandCoef k * Real.sqrt s + ∑ i ∈ range I, UpperDisagreement.capTerm (2 ^ i * s) ≤ 89 / 50 := by
  interval_cases k <;> simp only [bandBot, bandTop, bandCoef] at h1 h2 ⊢ <;> norm_num at h1 h2 ⊢
  · exact quarter_offset_0 s h1 h2 I
  · exact quarter_offset_1 s h1 h2 I
  · exact quarter_offset_2 s h1 h2 I
  · exact quarter_offset_3 s h1 h2 I

end QuarterSteps
section QuarterGridSum
open Real Uniform713

/-- The weights along the grid, for every gap. -/
theorem quarter_grid_le {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2) (K : ℕ) :
    ∑ l ∈ range K, Real.sqrt (cap l * d ^ 2) * quarterWeight l d ≤ 89 / 50 := by
  classical
  set f : ℕ → ℝ := fun l => Real.sqrt (cap l * d ^ 2) * quarterWeight l d with hf
  have hf0 : ∀ l, 0 ≤ f l := fun l => mul_nonneg (Real.sqrt_nonneg _) (quarterWeight_nonneg _ _)
  have hdd : 0 < d ^ 2 := by positivity
  have hd4 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hex : ∃ l, 19 / 20 ≤ cap l * d ^ 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((19 / 20) / d ^ 2) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by have := (div_lt_iff₀ hdd).1 hn; simp only [cap]; linarith⟩
  set M := Nat.find hex with hM
  have hMspec : 19 / 20 ≤ cap M * d ^ 2 := Nat.find_spec hex
  have hMmin : ∀ l < M, cap l * d ^ 2 < 19 / 20 := fun l hl => not_le.1 (Nat.find_min hex hl)
  have hM2 : 2 ≤ M := by
    by_contra h
    have hle : cap M ≤ 2 := by
      have := Tier2.Model.cap_mono (show M ≤ 1 by omega)
      simpa [cap] using this
    nlinarith
  obtain ⟨n, hn⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  set s := cap M * d ^ 2 with hs_def
  have hs2 : s ≤ 19 / 10 := by
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
    have hge : 19 / 20 ≤ cap (M + i) * d ^ 2 := by
      rw [hcap]
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    simp only [hf, quarterWeight, UpperDisagreement.capTerm]
    rw [ite_eq_left hge, hcap]
  rw [sum_congr rfl (fun i _ => hpost i)] at hext
  -- the band of the first grid point
  obtain ⟨k, hk, hlo, hhi⟩ : ∃ k < 4, bandBot k ≤ s ∧ s ≤ bandTop k := by
    rcases le_or_gt s (19 / 16) with h1 | h1
    · exact ⟨0, by norm_num, by simp only [bandBot]; norm_num; linarith, by simp only [bandTop]; norm_num; linarith⟩
    rcases le_or_gt s (57 / 40) with h2 | h2
    · exact ⟨1, by norm_num, by simp only [bandBot]; norm_num; linarith, by simp only [bandTop]; norm_num; linarith⟩
    rcases le_or_gt s (133 / 80) with h3 | h3
    · exact ⟨2, by norm_num, by simp only [bandBot]; norm_num; linarith, by simp only [bandTop]; norm_num; linarith⟩
    · exact ⟨3, by norm_num, by simp only [bandBot]; norm_num; linarith, by simp only [bandTop]; norm_num; linarith⟩
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
  have hbelow : ∑ l ∈ range M, f l ≤ bandCoef k * Real.sqrt s := by
    rw [← sum_range_reflect f M]
    have hterm : ∀ i ∈ range n, f (M - 1 - i) ≤
        Real.sqrt s * (rLevel ^ (i + 1) * (1 / 4 + bandStep k i)) := by
      intro i hi
      have hi' := mem_range.1 hi
      have hl1 : 1 ≤ M - 1 - i := by omega
      have hlt : cap (M - 1 - i) * d ^ 2 < 19 / 20 := hMmin _ (by omega)
      have hdrift : ∑ j ∈ range (M - 1 - i - 1), driftBound (M - 1 - i - 1) j d ≤ bandStep k i := by
        apply band_step_le k hk _ i hd
        have hc : cap M = cap (M - 1 - i - 1) * 2 ^ (i + 2) := by
          rw [show M = (M - 1 - i - 1) + (i + 2) by omega]
          simp only [cap, pow_add]
          rw [show M - 1 - i - 1 + (i + 2) - 1 - i - 1 = M - 1 - i - 1 by omega]
        have : cap (M - 1 - i - 1) * d ^ 2 * 2 ^ (i + 2) = s := by rw [hs_def, hc]; ring
        rw [le_div_iff₀ (by positivity)]
        linarith
      simp only [hf, quarterWeight]
      rw [ite_eq_right (not_le.2 hlt), ite_eq_left hl1, hroot i (by omega)]
      have hs0 : 0 ≤ Real.sqrt s * rLevel ^ (i + 1) :=
        mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg rLevel_pos.le _)
      calc
        _ ≤ Real.sqrt s * rLevel ^ (i + 1) * (1 / 4 + bandStep k i) := by gcongr
        _ = _ := by ring
    have h0 : f (M - 1 - n) ≤ Real.sqrt s * rLevel ^ (n + 1) := by
      have hl : M - 1 - n = 0 := by omega
      have hlt : cap 0 * d ^ 2 < 19 / 20 := hMmin 0 (by omega)
      simp only [hf]
      rw [hroot n (by omega)]
      rw [hl]
      simp only [quarterWeight]
      rw [ite_eq_right (not_le.2 hlt), ite_eq_right (by norm_num), mul_one]
    rw [hn, sum_range_succ]
    rw [← hn]
    have hS := sum_le_sum hterm
    rw [← mul_sum] at hS
    have hc := band_coef_le k hk n
    have hs0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    nlinarith [mul_le_mul_of_nonneg_left hc hs0]
  have hb := band_offset_le k hk s hlo hhi K
  linarith

end QuarterGridSum

end ThresholdHC.UpperQuarter
