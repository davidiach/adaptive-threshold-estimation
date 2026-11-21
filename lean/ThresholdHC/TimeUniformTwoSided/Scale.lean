import ThresholdHC.TimeUniformTwoSided.Specification
import ThresholdHC.Anytime.Width

/-! Comparison of the two inflation scales. The upper theorem uses
`Λ(n,δ) = log(1/δ) + 2 log(2 + log(1+n)/log 2)` and the lower theorem
`λ(n) = log(1/δ) + log log n`. For `n ≥ 3` and `0 < δ ≤ 1/4`,
`Λ(n,δ) ≤ 4 λ(n)`, so the selection functional at `n/Λ(n,δ)` is at most twice
its value at `n/λ(n)`. -/
noncomputable section
namespace ThresholdHC.TimeUniformTwoSided
open MeasureTheory Real
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.AnytimeLower

/-- `Λ(n,δ) ≤ 4 λ(n)` for `n ≥ 3` and `0 < δ ≤ 1/4`. -/
theorem inflation_le_four {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) {n : ℕ} (hn : 3 ≤ n) :
    ThresholdHC.Anytime.inflation (n:ℝ) δ ≤ 4*budgetInflation δ n := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  set x := log (n:ℝ) with hxdef
  have hx1 : 1 ≤ x := by
    have he := Real.exp_one_lt_d9
    exact ((Real.lt_log_iff_exp_lt hn0).mpr (by linarith)).le
  have hx0 : 0 < x := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2pos : 0 < log 2 := by linarith
  have h1n : log (1+(n:ℝ)) ≤ log 2+x := by
    rw [hxdef,← Real.log_mul (by norm_num) hn0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlb : log (1+(n:ℝ))/log 2 ≤ 1+(29/20)*x := by
    rw [div_le_iff₀ hl2pos]
    nlinarith
  have hlb0 : 0 ≤ log (1+(n:ℝ))/log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hl2pos.le
  have hpoly : 2+log (1+(n:ℝ))/log 2 ≤ 5*x^2 := by nlinarith
  have hlog : log (2+log (1+(n:ℝ))/log 2) ≤ log 5+2*log x := by
    have h := Real.log_le_log (by linarith) hpoly
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at h
    push_cast at h
    linarith
  have hℓ4 : log 4 ≤ log (1/δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have h25 : 2*log 5 ≤ 3*log 4 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 5^2) (by norm_num : (5:ℝ)^2 ≤ 4^3)
    rw [Real.log_pow,Real.log_pow] at h
    push_cast at h
    linarith
  unfold ThresholdHC.Anytime.inflation ThresholdHC.Anytime.logBudget budgetInflation
  rw [← hxdef]
  linarith

/-- The selection functional at `n/Λ(n,δ)` is at most twice its value at
`n/λ(n)` for `n ≥ 3`. -/
theorem inflation_selection_two (μ : Measure Gap) (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ4 : δ ≤ 1/4) {n : ℕ} (hn : 3 ≤ n) :
    ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ) ≤
      ENNReal.ofReal 2*ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hℓ : 0 < log (1/δ) := ThresholdHC.Confidence.confidence_log_pos hδ hδ4
  have hlogn : 1 ≤ log (n:ℝ) := by
    have he := Real.exp_one_lt_d9
    exact ((Real.lt_log_iff_exp_lt hn0).mpr (by linarith)).le
  have hll : 0 ≤ log (log (n:ℝ)) := Real.log_nonneg hlogn
  have hlam : 0 < budgetInflation δ n := by unfold budgetInflation; linarith
  have hLam : 0 < ThresholdHC.Anytime.inflation (n:ℝ) δ :=
    ThresholdHC.Anytime.inflation_pos hn0.le hδ hδ4
  have h4 := inflation_le_four hδ hδ4 hn
  have hone : (1:ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  by_cases hc : ThresholdHC.Anytime.inflation (n:ℝ) δ ≤ budgetInflation δ n
  · have hb : (n:ℝ)/budgetInflation δ n ≤ (n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ :=
      div_le_div_of_nonneg_left hn0.le hLam hc
    calc ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ)
        ≤ ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) :=
          ThresholdHC.Anytime.selection_antitone μ ρ (div_pos hn0 hlam) hb
      _ = 1*ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) := (one_mul _).symm
      _ ≤ _ := by gcongr
  · have hb : (n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ ≤ (n:ℝ)/budgetInflation δ n :=
      div_le_div_of_nonneg_left hn0.le hlam (le_of_not_ge hc)
    have hscale := ThresholdHC.HardBudget.selection_budget_scale μ ρ (div_pos hn0 hLam) hb
    have hratio : ((n:ℝ)/budgetInflation δ n)/((n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ) =
        ThresholdHC.Anytime.inflation (n:ℝ) δ/budgetInflation δ n := by
      field_simp
    have hsqrt : Real.sqrt (((n:ℝ)/budgetInflation δ n)/
        ((n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ)) ≤ 2 := by
      rw [hratio,Real.sqrt_le_left (by norm_num),div_le_iff₀ hlam]
      nlinarith
    exact hscale.trans (by gcongr)

/-- The upper envelope on the lower theorem's scale: `1500002 K(n/Λ(n,δ))` is
at most `3000004 K(n/λ(n))` for `n ≥ 3`. -/
theorem envelope_scale (μ : Measure Gap) (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    {n : ℕ} (hn : 3 ≤ n) :
    1500002*(ThresholdHC.EntropyTail.selection μ ρ
        ((n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ)).toReal ≤
      3000004*(ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n)).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ThresholdHC.HardBudget.finite_selection μ ρ _))
    (inflation_selection_two μ ρ hδ hδ4 hn)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by norm_num)] at h
  linarith

end ThresholdHC.TimeUniformTwoSided
