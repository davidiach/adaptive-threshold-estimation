import ThresholdHC.PowerQuantileRows.Rows
import ThresholdHC.PowerQuantileRows.AllExponents
import ThresholdHC.PowerQuantileRows.Bridges
import ThresholdHC.EntropyTailSharp.Full
import ThresholdHC.EntropyTailExecution.UpperTheorem

/-! Remark `rem:power-quantile` of `paper/v6/rare-events.tex` as Lean theorems.

The uniform rate (W7) is within `α`-dependent factors of each row of the
power-margin table (`power_row_rate`). With the quantile comparison of
`PowerWindow`, extended here to every exponent `α > 0` (`power_quantile_all`, a
Lean-only extension of v6 Theorem 14.13 for `α > 4`), the closed quantile
functional of an exact power law is the row within such factors
(`power_row_quantile`). The every-law comparison `10^{-17} Q ≤ R ≤ 30001 Q`
then gives the row for the minimax risk (`power_row_risk`). The separately
checked row theorems are not used; `Bridges` only identifies the inline row
formulas with their rate definitions. At `a = 1/4` the quadratic row is four
times the table entry inside the minimum (`quadratic_row_form`). -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PowerQuantileRows
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow
open ThresholdHC.EntropyTailQuantile

theorem power_row_rate : PowerRowRateStatement := by
  intro α hα
  rcases lt_trichotomy α 1 with h1 | h1 | h1
  · exact rate_lt_one hα h1
  · subst h1
    exact rate_one
  · rcases lt_trichotomy α 2 with h2 | h2 | h2
    · exact rate_between h1 h2
    · subst h2
      exact rate_two
    · exact rate_gt_two h2

theorem power_row_quantile : PowerRowQuantileStatement := by
  intro α hα
  obtain ⟨c, C, hc, hC, hrate⟩ := power_row_rate α hα
  refine ⟨c / Real.sqrt 2, 2 * C, by positivity, by positivity, ?_⟩
  intro μ _ a ρ B ha ha2 hρ hρ4 hB hm
  have hx : 0 < 1 / (a * Real.sqrt B) := by positivity
  obtain ⟨hl, hu⟩ := hrate ρ _ hρ hρ4 hx
  obtain ⟨ql, qu⟩ := power_quantile_all μ hα ha ha2 hρ hρ4 hB hm
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) ql
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hl (Real.sqrt_nonneg 2)
  · refine qu.trans (ENNReal.ofReal_le_ofReal ?_)
    linarith

theorem power_row_risk : PowerRowRiskStatement := by
  intro α hα
  obtain ⟨c, C, hc, hC, hQ⟩ := power_row_quantile α hα
  refine ⟨(10 : ℝ)⁻¹ ^ 17 * c, 30001 * C, by positivity, by positivity, ?_⟩
  intro μ _ a ρ B ha ha2 hρ hρ4 hB hm
  obtain ⟨hlo, hhi⟩ := hQ μ a ρ B ha ha2 hρ hρ4 hB hm
  constructor
  · have h := (mul_le_mul_right hlo (ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17))).trans
      (ThresholdHC.EntropyTailSharp.closed_quantile_lower_explicit μ hρ hρ4 hB)
    rw [← ENNReal.ofReal_mul (by positivity)] at h
    convert h using 1
    congr 1
    ring
  · have h := (ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001 μ hρ hρ4 hB).trans
      (mul_le_mul_right hhi (ENNReal.ofReal 30001))
    rw [← ENNReal.ofReal_mul (by norm_num)] at h
    convert h using 1
    congr 1
    ring

theorem quadratic_row_form : QuadraticRowFormStatement := by
  intro ρ B hρ hρ4 hB
  rw [powerRow_two]
  congr 1
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hcrit := critical_factor_ge_one hρ hρ4
  rw [Real.sqrt_div (by positivity)]
  field_simp

end ThresholdHC.PowerQuantileRows
