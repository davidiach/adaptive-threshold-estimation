import ThresholdHC.HardBudget.Application

noncomputable section
open MeasureTheory
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier6 ThresholdHC.BlindUpper

theorem budget_scale {b B : ℝ} (hb : 0 < b) (hB : b ≤ B) :
    1 ≤ Real.sqrt (B/b) ∧ 1/Real.sqrt b = Real.sqrt (B/b)*(1/Real.sqrt B) := by
  have hB0 := hb.trans_le hB
  refine ⟨?_,?_⟩
  · exact Real.one_le_sqrt.mpr ((one_le_div hb).mpr hB)
  · rw [Real.sqrt_div hB0.le]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hb),ne_of_gt (Real.sqrt_pos.mpr hB0)]

theorem min_one_scaled (a x : ℝ) (ha : 1 ≤ a) : min 1 (a*x) ≤ a*min 1 x := by
  by_cases h : x ≤ 1
  · rw [min_eq_right h]; exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge h),mul_one]; exact (min_le_left _ _).trans ha

theorem ordinary_budget_scale (μ : Measure Gap) [IsProbabilityMeasure μ] {b B : ℝ}
    (hb : 0 < b) (hB : b ≤ B) :
    modulus μ (1/Real.sqrt b) ≤ Real.sqrt (B/b)*modulus μ (1/Real.sqrt B) := by
  obtain ⟨ha,he⟩ := budget_scale hb hB
  unfold modulus
  rw [← integral_const_mul]
  apply integral_mono (integrable_clippedGap μ (by positivity))
    ((integrable_clippedGap μ (by positivity : 0 ≤ 1/Real.sqrt B)).const_mul _)
  intro d
  unfold clippedGap
  rw [he,mul_div_assoc]
  exact min_one_scaled _ _ ha

theorem half_le_inverse_sqrt {B : ℝ} (hb : 0 < B) (hu : B < 4) : 1/2 ≤ 1/Real.sqrt B := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
  nlinarith [Real.sq_sqrt hb.le,Real.sqrt_nonneg B]

end ThresholdHC.HardBudget
