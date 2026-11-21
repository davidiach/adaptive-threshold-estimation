import ThresholdHC.UnknownLawConfidence.Specification

/-! The integer threshold `H(k,e)` and the stage sizes.

`H(k,e)` satisfies `k * ceil(log2(1/e)) <= 2 H^2` and `H < sqrt(k ceil(log2(1/e))/2) + 1`.
A one-sided deviation of `H/k` in `k` trials therefore has Hoeffding bound
`exp(-2H^2/k) <= e`. Every stage has `2 <= n`, `j + 1 <= n <= m` and `n m <= c_j`. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Real
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.HardBudget

theorem hoeffdingCount_spec (k : ℕ) (e : ℝ) :
    k * ⌈Real.logb 2 (1 / e)⌉₊ ≤ 2 * hoeffdingCount k e ^ 2 := by
  apply Nat.sInf_mem (s := {H : ℕ | k * ⌈Real.logb 2 (1 / e)⌉₊ ≤ 2 * H ^ 2})
  refine ⟨k * ⌈Real.logb 2 (1 / e)⌉₊, ?_⟩
  change _ ≤ 2 * _ ^ 2
  have h := Nat.le_mul_self (k * ⌈Real.logb 2 (1 / e)⌉₊)
  nlinarith

theorem hoeffdingCount_le {k : ℕ} {e : ℝ} {h : ℕ}
    (hh : k * ⌈Real.logb 2 (1 / e)⌉₊ ≤ 2 * h ^ 2) : hoeffdingCount k e ≤ h :=
  Nat.sInf_le hh

theorem hoeffdingCount_lt (k : ℕ) (e : ℝ) :
    (hoeffdingCount k e : ℝ) <
      Real.sqrt ((k : ℝ) * (⌈Real.logb 2 (1 / e)⌉₊ : ℝ) / 2) + 1 := by
  set x : ℝ := (k : ℝ) * (⌈Real.logb 2 (1 / e)⌉₊ : ℝ) / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hc : Real.sqrt x ≤ (⌈Real.sqrt x⌉₊ : ℝ) := Nat.le_ceil _
  have hsq : x ≤ (⌈Real.sqrt x⌉₊ : ℝ) ^ 2 := by
    calc x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx0).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
  have hle : hoeffdingCount k e ≤ ⌈Real.sqrt x⌉₊ := by
    apply hoeffdingCount_le
    have : ((k * ⌈Real.logb 2 (1 / e)⌉₊ : ℕ) : ℝ) ≤ ((2 * ⌈Real.sqrt x⌉₊ ^ 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  calc (hoeffdingCount k e : ℝ) ≤ (⌈Real.sqrt x⌉₊ : ℝ) := by exact_mod_cast hle
    _ < Real.sqrt x + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)

/-- The Hoeffding exponent at deviation `H(k,e)/k` is at most `e`. -/
theorem hoeffding_exp_le {k : ℕ} (hk : 0 < k) {e : ℝ} (he : 0 < e) :
    Real.exp (-2 * (k : ℝ) * ((hoeffdingCount k e : ℝ) / k) ^ 2) ≤ e := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmain0 : ((k * ⌈Real.logb 2 (1 / e)⌉₊ : ℕ) : ℝ) ≤
      ((2 * hoeffdingCount k e ^ 2 : ℕ) : ℝ) := by exact_mod_cast hoeffdingCount_spec k e
  push_cast at hmain0
  set H : ℝ := (hoeffdingCount k e : ℝ)
  set L : ℝ := (⌈Real.logb 2 (1 / e)⌉₊ : ℝ)
  have hL : Real.logb 2 (1 / e) ≤ L := Nat.le_ceil _
  have hmain : (k : ℝ) * L ≤ 2 * H ^ 2 := hmain0
  have hkey : -2 * (k : ℝ) * (H / k) ^ 2 = -(2 * H ^ 2 / k) := by
    field_simp
  have hdiv : L ≤ 2 * H ^ 2 / k := by
    rw [le_div_iff₀ hkR]
    linarith
  rw [hkey]
  by_cases he1 : 1 ≤ e
  · calc Real.exp (-(2 * H ^ 2 / k)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by have : 0 ≤ 2 * H ^ 2 / k := by positivity
                                  linarith)
      _ = 1 := Real.exp_zero
      _ ≤ e := he1
  · have he1' : e < 1 := lt_of_not_ge he1
    have hlog : 0 < Real.log (1 / e) := by
      apply Real.log_pos
      rw [lt_div_iff₀ he]
      linarith
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hb : Real.log (1 / e) ≤ Real.logb 2 (1 / e) := by
      rw [Real.logb, le_div_iff₀ h2']
      nlinarith
    calc Real.exp (-(2 * H ^ 2 / k)) ≤ Real.exp (-Real.log (1 / e)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = e := by
          rw [one_div, Real.log_inv, neg_neg, Real.exp_log he]

theorem stageCap_eq (j : ℕ) : stageCap j = 4 * 2 ^ j := rfl

theorem succ_mul_self_le (j : ℕ) : (j + 1) * (j + 1) ≤ 4 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have h := Nat.lt_two_pow_self (n := j)
    rw [pow_succ]
    nlinarith

theorem succ_le_itemCount (j : ℕ) : j + 1 ≤ itemCount j :=
  Nat.le_sqrt.mpr (succ_mul_self_le j)

theorem two_le_itemCount (j : ℕ) : 2 ≤ itemCount j := by
  apply Nat.le_sqrt.mpr
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  change 2 * 2 ≤ 4 * 2 ^ j
  omega

theorem itemCount_pos (j : ℕ) : 0 < itemCount j := by
  have := two_le_itemCount j
  omega

theorem itemCount_le_flipCount (j : ℕ) : itemCount j ≤ flipCount j :=
  (Nat.le_div_iff_mul_le (itemCount_pos j)).mpr (Nat.sqrt_le _)

theorem flipCount_pos (j : ℕ) : 0 < flipCount j :=
  (itemCount_pos j).trans_le (itemCount_le_flipCount j)

theorem itemCount_mul_flipCount_le (j : ℕ) : itemCount j * flipCount j ≤ stageCap j :=
  Nat.mul_div_le _ _

theorem tolerance_pos (j : ℕ) : 0 < tolerance j := by
  have := itemCount_pos j
  unfold tolerance
  positivity

theorem tolerance_le_half (j : ℕ) : tolerance j ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ itemCount j := by exact_mod_cast two_le_itemCount j
  unfold tolerance
  exact one_div_le_one_div_of_le (by norm_num) h

theorem radius_nonneg (j : ℕ) : 0 ≤ radius j := by
  unfold radius
  positivity

theorem sampling_nonneg (δ : ℝ) (j : ℕ) : 0 ≤ sampling δ j := by
  unfold sampling
  positivity

end ThresholdHC.UnknownLawConfidence
