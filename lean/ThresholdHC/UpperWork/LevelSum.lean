import ThresholdHC.UpperWork.Survival

/-! The level sum of the expected work with the sharper per-level bound.

Each level's expected work is at most its cap, and at most
`(49/10)*d⁻²*(1 + log (cap l*d^2))` once `cap l*d^2 ≥ 1` (`Survival`). The
levels whose `cap l*d^2` is at most 32 are summed with the cap; the rest, with
the logarithmic bound. With `q^2 = cap m*d^2` for the last level `m` of the
first kind, the two parts are at most `q/d` and `A/(q*d)` with
`A = (49/10)*r*(1 + 5*log 2 + log 2/(1 - r))`, `r = 2^{-1/2}`. Since
`16 < q^2 ≤ 32` and `4*sqrt 32 ≤ A`, their sum is at most `(4 + A/4)/d`, and
`A < 23.68` gives the constant `248/25`. This replaces the bound
`(17/7)*31 = 527/7` that the factor 17 gives with `Uniform713.Series`. -/
noncomputable section
namespace ThresholdHC.UpperWork
open Real Finset ThresholdHC.Uniform713

theorem rLevel_mul_sqrt_two : rLevel * Real.sqrt 2 = 1 := by
  unfold rLevel
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by norm_num))

theorem sqrt_cap (l : ℕ) : Real.sqrt (cap l) = Real.sqrt 2 ^ l := by
  rw [Real.sqrt_eq_iff_eq_sq (cap_pos l).le (by positivity), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt (by norm_num)]
  rfl

/-- The levels summed with their caps: exactly `sqrt 2^n - r`. -/
theorem levelWeight_cap_sum (n : ℕ) :
    ∑ l ∈ range (n + 1), pLevel l * cap l = Real.sqrt 2 ^ n - rLevel := by
  have hr : rLevel * Real.sqrt 2 = 1 := rLevel_mul_sqrt_two
  have hterm : ∀ l, pLevel l * cap l = (1 - rLevel) * Real.sqrt 2 ^ l := by
    intro l
    have h2 : cap l = Real.sqrt 2 ^ l * Real.sqrt 2 ^ l := by
      rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
      rfl
    have h1 : rLevel ^ l * Real.sqrt 2 ^ l = 1 := by rw [← mul_pow, hr, one_pow]
    rw [h2]
    unfold pLevel
    calc
      (1 - rLevel) * rLevel ^ l * (Real.sqrt 2 ^ l * Real.sqrt 2 ^ l) =
          (1 - rLevel) * (rLevel ^ l * Real.sqrt 2 ^ l) * Real.sqrt 2 ^ l := by ring
      _ = _ := by rw [h1]; ring
  simp_rw [hterm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    linear_combination (-(Real.sqrt 2 ^ n)) * hr

theorem arith_geom_sum_le (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∑ i ∈ range n, rLevel ^ i * (a + ((i : ℝ) + 1) * b) ≤
      a / (1 - rLevel) + b / (1 - rLevel) ^ 2 := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hnorm : ‖rLevel‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have h0 := (hasSum_geometric_of_lt_one hr0.le hr1).mul_left (a + b)
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left b
  have hs : HasSum (fun i : ℕ => rLevel ^ i * (a + ((i : ℝ) + 1) * b))
      (a / (1 - rLevel) + b / (1 - rLevel) ^ 2) := by
    convert h0.add h1 using 1
    · ext i
      ring
    · have hne : 1 - rLevel ≠ 0 := ne_of_gt (sub_pos.2 hr1)
      field_simp
      ring
  exact sum_le_hasSum (range n)
    (fun i _ => mul_nonneg (pow_nonneg hr0.le i) (by positivity)) hs

/-- The constant of the logarithmic part, in closed form. -/
theorem levelSum_constant_eq :
    (49 / 10) * rLevel * ((1 + 5 * Real.log 2) + Real.log 2 / (1 - rLevel)) =
      (49 / 10) * ((1 + 5 * Real.log 2) * Real.sqrt 2 / 2 + Real.log 2 * (Real.sqrt 2 + 1)) := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have hr : rLevel = Real.sqrt 2 / 2 := by
    unfold rLevel
    field_simp
    linarith
  have hinv : 1 / (1 - rLevel) = 2 + Real.sqrt 2 := by
    rw [hr]
    have hne : 1 - Real.sqrt 2 / 2 ≠ 0 := by nlinarith
    rw [div_eq_iff hne]
    linear_combination (1 / 2) * hσ
  rw [div_eq_mul_one_div (Real.log 2), hinv, hr]
  linear_combination (49 / 10) * (Real.log 2 / 2) * hσ

theorem levelSum_constant_bounds :
    (283 / 50) * 4 ≤ (49 / 10) * rLevel * ((1 + 5 * Real.log 2) + Real.log 2 / (1 - rLevel)) ∧
    (49 / 10) * rLevel * ((1 + 5 * Real.log 2) + Real.log 2 / (1 - rLevel)) ≤
      4 * (248 / 25 - 4) := by
  rw [levelSum_constant_eq]
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hll := Real.log_two_gt_d9
  have hlu := Real.log_two_lt_d9
  have hl0 : 0 ≤ Real.log 2 := by linarith
  constructor
  · nlinarith [mul_le_mul hσl hll.le (by norm_num) (by positivity)]
  · nlinarith [mul_le_mul hσu hlu.le hl0 (by norm_num)]

/-- The sharper level sum of the expected work. -/
theorem work_levelSum_le (L : ℕ) (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1 / 2) (w : ℕ → ℝ)
    (hcap : ∀ l ≤ L, w l ≤ cap l)
    (hlog : ∀ l ≤ L, 1 ≤ cap l * d ^ 2 →
      w l ≤ (49 / 10) * (d⁻¹) ^ 2 * (1 + Real.log (cap l * d ^ 2))) :
    ∑ l ∈ range (L + 1), pLevel l * w l ≤ (248 / 25) * min (Real.sqrt (cap L)) d⁻¹ := by
  classical
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hp : ∀ l, 0 < pLevel l := fun l => mul_pos (sub_pos.2 hr1) (pow_pos hr0 l)
  have hd2 : 0 < d ^ 2 := by positivity
  have hpre : ∀ n, ∑ l ∈ range (n + 1), pLevel l * cap l ≤ Real.sqrt (cap n) := by
    intro n
    rw [levelWeight_cap_sum, sqrt_cap]
    linarith
  by_cases hL : cap L * d ^ 2 ≤ 32
  · have h1 : ∑ l ∈ range (L + 1), pLevel l * w l ≤ Real.sqrt (cap L) :=
      (sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left
        (hcap l (Nat.le_of_lt_succ (mem_range.1 hl))) (hp l).le)).trans (hpre L)
    refine h1.trans ?_
    rw [mul_min_of_nonneg _ _ (by norm_num)]
    apply le_min
    · nlinarith [Real.sqrt_nonneg (cap L)]
    · have hs : Real.sqrt (cap L) * d ≤ 6 := by
        rw [show Real.sqrt (cap L) * d = Real.sqrt (cap L * d ^ 2) by
          rw [Real.sqrt_mul (cap_pos L).le, Real.sqrt_sq hd.le]]
        rw [Real.sqrt_le_left (by norm_num)]
        linarith
      rw [← div_eq_mul_inv, le_div_iff₀ hd]
      linarith
  · have hL' : 32 < cap L * d ^ 2 := lt_of_not_ge hL
    have hex : ∃ k, 32 < cap k * d ^ 2 := ⟨L, hL'⟩
    have hK1L : Nat.find hex ≤ L := Nat.find_min' hex hL'
    have hK1 : Nat.find hex ≠ 0 := by
      intro h0
      have h := Nat.find_spec hex
      rw [h0, cap_zero, one_mul] at h
      nlinarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hK1
    have hθhi : cap m * d ^ 2 ≤ 32 := not_lt.1 (Nat.find_min hex (by omega))
    have hθlo : 16 < cap m * d ^ 2 := by
      have h := Nat.find_spec hex
      rw [hm, cap_succ] at h
      linarith
    have hmL : m + 1 ≤ L := by omega
    have hsm : 0 < Real.sqrt (cap m) := Real.sqrt_pos.2 (cap_pos m)
    set q := Real.sqrt (cap m) * d with hq_def
    have hq2 : q ^ 2 = cap m * d ^ 2 := by rw [hq_def, mul_pow, Real.sq_sqrt (cap_pos m).le]
    have hq0 : 0 < q := mul_pos hsm hd
    have hq4 : 4 < q := by nlinarith
    have hq6 : q < 283 / 50 := by nlinarith
    have hsplit : L + 1 = (m + 1) + (L - m) := by omega
    rw [hsplit, sum_range_add]
    have hP : ∑ l ∈ range (m + 1), pLevel l * w l ≤ q / d := by
      have h := (sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left
        (hcap l (by have := mem_range.1 hl; omega)) (hp l).le)).trans (hpre m)
      calc
        _ ≤ Real.sqrt (cap m) := h
        _ = q / d := by rw [hq_def]; field_simp
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hT : ∑ i ∈ range (L - m), pLevel (m + 1 + i) * w (m + 1 + i) ≤
        ((49 / 10) * (d⁻¹) ^ 2 * ((1 - rLevel) * rLevel ^ (m + 1))) *
          ∑ i ∈ range (L - m), rLevel ^ i * ((1 + 5 * Real.log 2) + ((i : ℝ) + 1) * Real.log 2) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have hi' := mem_range.1 hi
      have hl : m + 1 + i ≤ L := by omega
      have hcapl : cap (m + 1 + i) * d ^ 2 = 2 ^ (i + 1) * (cap m * d ^ 2) := by
        simp only [cap]
        ring
      have hpow : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
      have hx1 : 1 ≤ cap (m + 1 + i) * d ^ 2 := by rw [hcapl]; nlinarith
      have hlogle : Real.log (cap (m + 1 + i) * d ^ 2) ≤ ((i : ℝ) + 6) * Real.log 2 := by
        have hle : cap (m + 1 + i) * d ^ 2 ≤ 2 ^ (i + 6) := by
          rw [hcapl, show (2 : ℝ) ^ (i + 6) = 2 ^ (i + 1) * 32 by ring]
          exact mul_le_mul_of_nonneg_left hθhi (by positivity)
        have h := Real.log_le_log (by positivity) hle
        rw [Real.log_pow] at h
        push_cast at h
        linarith
      have hw := hlog (m + 1 + i) hl hx1
      have hpl : pLevel (m + 1 + i) = (1 - rLevel) * rLevel ^ (m + 1) * rLevel ^ i := by
        unfold pLevel
        rw [pow_add]
        ring
      rw [hpl]
      have hpos : 0 ≤ (1 - rLevel) * rLevel ^ (m + 1) * rLevel ^ i :=
        mul_nonneg (mul_nonneg (sub_pos.2 hr1).le (pow_nonneg hr0.le _)) (pow_nonneg hr0.le _)
      have hw' : w (m + 1 + i) ≤ (49 / 10) * (d⁻¹) ^ 2 * (1 + ((i : ℝ) + 6) * Real.log 2) :=
        hw.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      calc
        (1 - rLevel) * rLevel ^ (m + 1) * rLevel ^ i * w (m + 1 + i) ≤
            (1 - rLevel) * rLevel ^ (m + 1) * rLevel ^ i *
              ((49 / 10) * (d⁻¹) ^ 2 * (1 + ((i : ℝ) + 6) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hw' hpos
        _ = _ := by ring
    have hG := arith_geom_sum_le (L - m) (a := 1 + 5 * Real.log 2) (b := Real.log 2)
      (by positivity) hlog2.le
    have hcoef0 : 0 ≤ (49 / 10) * (d⁻¹) ^ 2 * ((1 - rLevel) * rLevel ^ (m + 1)) :=
      mul_nonneg (by positivity) (mul_nonneg (sub_pos.2 hr1).le (pow_nonneg hr0.le _))
    have hT' := hT.trans (mul_le_mul_of_nonneg_left hG hcoef0)
    set A := (49 / 10) * rLevel * ((1 + 5 * Real.log 2) + Real.log 2 / (1 - rLevel)) with hA_def
    have hrm : rLevel ^ m = d / q := by
      have h : rLevel ^ m * Real.sqrt (cap m) = 1 := by
        rw [sqrt_cap, ← mul_pow, rLevel_mul_sqrt_two, one_pow]
      rw [hq_def]
      field_simp
      linarith
    have hTA : ((49 / 10) * (d⁻¹) ^ 2 * ((1 - rLevel) * rLevel ^ (m + 1))) *
        ((1 + 5 * Real.log 2) / (1 - rLevel) + Real.log 2 / (1 - rLevel) ^ 2) = A / (q * d) := by
      have hne : 1 - rLevel ≠ 0 := ne_of_gt (sub_pos.2 hr1)
      rw [pow_succ rLevel m, hrm, hA_def]
      field_simp
    rw [hTA] at hT'
    obtain ⟨hAlo, hAhi⟩ := levelSum_constant_bounds
    rw [← hA_def] at hAlo hAhi
    have hkey : q + A / q ≤ 4 + A / 4 := by
      have he : q + A / q - (4 + A / 4) = (q - 4) * (4 * q - A) / (4 * q) := by
        field_simp
        ring
      have hnum : (q - 4) * (4 * q - A) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have h := div_nonpos_of_nonpos_of_nonneg hnum (by positivity : (0 : ℝ) ≤ 4 * q)
      linarith
    have hmin : min (Real.sqrt (cap L)) d⁻¹ = d⁻¹ := by
      apply min_eq_right
      rw [← one_div, div_le_iff₀ hd]
      have h : Real.sqrt (cap L) * d = Real.sqrt (cap L * d ^ 2) := by
        rw [Real.sqrt_mul (cap_pos L).le, Real.sqrt_sq hd.le]
      rw [h]
      exact Real.le_sqrt_of_sq_le (by linarith)
    rw [hmin]
    calc
      _ ≤ q / d + A / (q * d) := add_le_add hP hT'
      _ = (q + A / q) / d := by field_simp
      _ ≤ (4 + A / 4) / d := div_le_div_of_nonneg_right hkey hd.le
      _ ≤ (248 / 25) / d := div_le_div_of_nonneg_right (by linarith) hd.le
      _ = _ := by rw [div_eq_mul_inv]

end ThresholdHC.UpperWork
