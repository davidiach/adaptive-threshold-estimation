import ThresholdHC.Statements2
import ThresholdHC.Uniform713.Series

noncomputable section

namespace ThresholdHC.Tier2

open ThresholdHC Uniform713 Finset

/-- A finite second-moment envelope transfers to the Tier 2 constant. -/
theorem finite_secondMoment_bound (L : ℕ) (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1 / 2)
    (e : ℕ → ℝ)
    (he : ∀ l ≤ L, e l ≤ min 1 (3 / (cap l * d ^ 2) ^ 2)) :
    (∑ l ∈ range (L + 1), e l / pLevel l) ≤
      85 * min (Real.sqrt (cap L)) d⁻¹ := by
  have hle : (∑ l ∈ range (L + 1), e l / pLevel l) ≤
      ∑ l ∈ range (L + 1), secondMomentEnvelope l d := by
    apply sum_le_sum
    intro l hl
    have hlL : l ≤ L := Nat.le_of_lt_succ (mem_range.mp hl)
    exact div_le_div_of_nonneg_right (he l hlL) (levelProb_pos l).le
  have hs := sum_secondMomentEnvelope_lt L d hd hdhalf
  have hn : 0 ≤ min (Real.sqrt (cap L)) d⁻¹ :=
    le_min (Real.sqrt_nonneg _) (inv_nonneg.mpr hd.le)
  have hconst : (23 : ℝ) * min (Real.sqrt (cap L)) d⁻¹ ≤
      85 * min (Real.sqrt (cap L)) d⁻¹ := mul_le_mul_of_nonneg_right (by norm_num) hn
  exact (hle.trans (by simpa only [one_div] using hs.le)).trans hconst

/-- Shared-prefix monotonicity reduces level work to one classifier envelope. -/
theorem finite_workMoment_bound (L : ℕ) (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1 / 2)
    (w : ℕ → ℝ) (hw : ∀ l ≤ L, w l ≤ 17 * workEnvelope l d) :
    (∑ l ∈ range (L + 1), pLevel l * w l) ≤
      149 * min (Real.sqrt (cap L)) d⁻¹ := by
  have hle : (∑ l ∈ range (L + 1), pLevel l * w l) ≤
      (17 / 7 : ℝ) * ∑ l ∈ range (L + 1), levelProb l * (7 * workEnvelope l d) := by
    rw [mul_sum]
    apply sum_le_sum
    intro l hl
    have hlL : l ≤ L := Nat.le_of_lt_succ (mem_range.mp hl)
    have h := mul_le_mul_of_nonneg_left (hw l hlL) (levelProb_pos l).le
    convert h using 1 <;> simp only [pLevel, levelProb] <;> ring
  have hs := mul_le_mul_of_nonneg_left (sum_weightedWorkEnvelope_lt L d hd hdhalf).le
    (by norm_num : (0 : ℝ) ≤ 17 / 7)
  have hn : 0 ≤ min (Real.sqrt (cap L)) d⁻¹ :=
    le_min (Real.sqrt_nonneg _) (inv_nonneg.mpr hd.le)
  have hconst : (17 / 7 : ℝ) * (31 * min (Real.sqrt (cap L)) d⁻¹) ≤
      149 * min (Real.sqrt (cap L)) d⁻¹ := by nlinarith
  exact (hle.trans (by simpa only [one_div] using hs)).trans hconst

end ThresholdHC.Tier2

