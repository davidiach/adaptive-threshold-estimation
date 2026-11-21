import ThresholdHC.FiniteGapCorollaries.Specification
import ThresholdHC.FiniteQuantile.Full
import ThresholdHC.EntropyTailSharp.Full
import ThresholdHC.EntropyTail.SingleAtom

/-! The finite-gap corollaries. At a point mass the selection functional is the
single-gap rate, so the explicit entropy–tail law gives the one-gap form. The
closed quantile value is `min{ρ, x + y}` with `x = T_h` and
`y^2 = ρ Γ_κ / B`, and `x^2 + y^2 ≤ (x + y)^2 ≤ 2(x^2 + y^2)`, so squaring the
finite-law bounds gives the mean-square form. When `h` is at most every atom,
`min{1, h/d} = h/d` on the support, which carries the quantile tail, so
`T_h = h J_ν`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.FiniteGapCorollaries
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

theorem one_gap (d : Gap) (ρ B : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17 * aboveTwoRate (d : ℝ) ρ B) ≤
        rareMinimaxRisk (Measure.dirac d) ρ B ∧
      rareMinimaxRisk (Measure.dirac d) ρ B ≤ ENNReal.ofReal (28000 * aboveTwoRate (d : ℝ) ρ B) := by
  obtain ⟨hlo, hup⟩ := EntropyTailSharp.entropy_tail_explicit_law (Measure.dirac d) ρ B hρ hρ4 hB
  rw [EntropyTail.single_atom ρ B hρ hρ4 hB d] at hlo hup
  have hr : 0 ≤ aboveTwoRate (d : ℝ) ρ B := by
    unfold aboveTwoRate
    exact le_min hρ.le (div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg d.property.1.le (Real.sqrt_nonneg _)))
  constructor
  · rwa [ENNReal.ofReal_mul (by positivity)]
  · rwa [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

theorem sq_add_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  have h : ((x : ℝ) + y) ^ 2 ≤ 2 * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((x : ℝ) - y)]
  have h' : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    rw [← NNReal.coe_le_coe]; push_cast; exact h
  exact_mod_cast h'

theorem le_sq_add (x y : ℝ≥0∞) : x ^ 2 + y ^ 2 ≤ (x + y) ^ 2 := by
  rw [add_sq]
  calc x ^ 2 + y ^ 2 = x ^ 2 + 0 + y ^ 2 := by rw [add_zero]
    _ ≤ x ^ 2 + 2 * x * y + y ^ 2 := by gcongr; exact zero_le

theorem min_sq (a b : ℝ≥0∞) : (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ zero_le h 2)]
  · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ zero_le h 2)]

theorem closed_quantile_sq (μ : Measure Gap) (ρ B : ℝ) (hB : 0 < B) :
    let M := min (ENNReal.ofReal ρ ^ 2)
      (ENNReal.ofReal (tailModulus (quantileTail μ ρ) (EntropyTailQuantile.budgetScale B)) ^ 2 +
        ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ) / ENNReal.ofReal B)
    M ≤ (closedQuantileValue μ ρ B) ^ 2 ∧ (closedQuantileValue μ ρ B) ^ 2 ≤ 2 * M := by
  intro M
  set x := ENNReal.ofReal (tailModulus (quantileTail μ ρ) (EntropyTailQuantile.budgetScale B))
  set y := ENNReal.ofReal (EntropyTailQuantile.budgetScale B) *
    (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/(2:ℝ))
  have hy : y ^ 2 = ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ) / ENNReal.ofReal B := by
    simp only [y, mul_pow]
    rw [← ENNReal.rpow_natCast ((ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/(2:ℝ))),
      ← ENNReal.rpow_mul]
    norm_num
    rw [← ENNReal.ofReal_pow (by unfold EntropyTailQuantile.budgetScale; positivity)]
    have hb : EntropyTailQuantile.budgetScale B ^ 2 = B⁻¹ := by
      unfold EntropyTailQuantile.budgetScale; rw [inv_pow, Real.sq_sqrt hB.le]
    rw [hb, ENNReal.ofReal_inv_of_pos hB, div_eq_mul_inv, mul_comm]
  have hQ : closedQuantileValue μ ρ B = min (ENNReal.ofReal ρ) (x + y) := rfl
  rw [hQ, min_sq]
  constructor
  · apply min_le_min le_rfl
    rw [← hy]; exact le_sq_add x y
  · calc min (ENNReal.ofReal ρ ^ 2) ((x + y) ^ 2)
        ≤ min (2 * ENNReal.ofReal ρ ^ 2) (2 * (x ^ 2 + y ^ 2)) := by
          apply min_le_min _ (sq_add_le x y)
          calc ENNReal.ofReal ρ ^ 2 = 1 * ENNReal.ofReal ρ ^ 2 := (one_mul _).symm
            _ ≤ 2 * ENNReal.ofReal ρ ^ 2 := by gcongr; norm_num
      _ = 2 * M := by
          rw [← mul_min, hy]

theorem mean_square (μ : Measure Gap) [IsProbabilityMeasure μ] (hfin : μ.support.Finite)
    (ρ B : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    let M := min (ENNReal.ofReal ρ ^ 2)
      (ENNReal.ofReal (tailModulus (quantileTail μ ρ) (EntropyTailQuantile.budgetScale B)) ^ 2 +
        ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ) / ENNReal.ofReal B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M ≤ (rareMinimaxRisk μ ρ B) ^ 2 ∧
      (rareMinimaxRisk μ ρ B) ^ 2 ≤ 2 * 30001 ^ 2 * M := by
  intro M
  obtain ⟨hlo, hup⟩ := FiniteQuantile.direct_finite_law μ hfin ρ B hρ hρ4 hB
  obtain ⟨hM1, hM2⟩ := closed_quantile_sq μ ρ B hB
  constructor
  · calc ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M
        ≤ ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * (closedQuantileValue μ ρ B) ^ 2 := by gcongr
      _ = (ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) * closedQuantileValue μ ρ B) ^ 2 := by rw [mul_pow]
      _ ≤ (rareMinimaxRisk μ ρ B) ^ 2 := by gcongr
  · calc (rareMinimaxRisk μ ρ B) ^ 2 ≤ (30001 * closedQuantileValue μ ρ B) ^ 2 := by gcongr
      _ = 30001 ^ 2 * (closedQuantileValue μ ρ B) ^ 2 := by rw [mul_pow]
      _ ≤ 30001 ^ 2 * (2 * M) := by gcongr
      _ = 2 * 30001 ^ 2 * M := by ring

/-- The quantile tail is absolutely continuous with respect to the law. -/
theorem quantileTail_ac (μ : Measure Gap) (ρ : ℝ) : quantileTail μ ρ ≪ μ := by
  unfold quantileTail
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).add_left
    ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _)

/-- If `h` is at most every gap in the support, `T_h = h J_ν`. -/
theorem tail_linear (μ : Measure Gap) (ρ h : ℝ)
    (hsupp : ∀ d ∈ μ.support, h ≤ (d : ℝ)) :
    tailModulus (quantileTail μ ρ) h = h * ∫ d : Gap, (d : ℝ)⁻¹ ∂(quantileTail μ ρ) := by
  unfold tailModulus
  rw [← integral_const_mul]
  apply integral_congr_ae
  have hae : ∀ᵐ d ∂μ, d ∈ μ.support := Measure.support_mem_ae
  filter_upwards [(quantileTail_ac μ ρ).ae_le hae] with d hd
  have hd0 : 0 < (d : ℝ) := d.property.1
  have : h / (d : ℝ) ≤ 1 := (div_le_one hd0).2 (hsupp d hd)
  rw [min_eq_right this, div_eq_mul_inv]

theorem large_budget_mean_square (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hfin : μ.support.Finite) (ρ B : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hlarge : ∀ d ∈ μ.support, ((d : ℝ) ^ 2)⁻¹ ≤ B) :
    let J := ∫ d : Gap, (d : ℝ)⁻¹ ∂(quantileTail μ ρ)
    let M := min (ENNReal.ofReal ρ ^ 2)
      ((ENNReal.ofReal J ^ 2 + ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) /
        ENNReal.ofReal B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M ≤ (rareMinimaxRisk μ ρ B) ^ 2 ∧
      (rareMinimaxRisk μ ρ B) ^ 2 ≤ 2 * 30001 ^ 2 * M := by
  intro J M
  have hh : ∀ d ∈ μ.support, EntropyTailQuantile.budgetScale B ≤ (d : ℝ) := by
    intro d hd
    have hd0 : 0 < (d : ℝ) := d.property.1
    have h2 := hlarge d hd
    unfold EntropyTailQuantile.budgetScale
    rw [inv_le_comm₀ (Real.sqrt_pos.2 hB) hd0, ← Real.sqrt_sq (inv_nonneg.2 hd0.le)]
    exact Real.sqrt_le_sqrt (by rw [inv_pow]; exact h2)
  have hT := tail_linear μ ρ _ hh
  have hJ : 0 ≤ J := integral_nonneg (fun d => inv_nonneg.2 d.property.1.le)
  have hs : 0 ≤ EntropyTailQuantile.budgetScale B := by
    unfold EntropyTailQuantile.budgetScale; positivity
  have hM : M = min (ENNReal.ofReal ρ ^ 2)
      (ENNReal.ofReal (tailModulus (quantileTail μ ρ) (EntropyTailQuantile.budgetScale B)) ^ 2 +
        ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ) / ENNReal.ofReal B) := by
    simp only [M]
    congr 1
    rw [ENNReal.add_div, hT]
    congr 1
    rw [← ENNReal.ofReal_pow (mul_nonneg hs hJ), ← ENNReal.ofReal_pow hJ,
      ← ENNReal.ofReal_div_of_pos hB, mul_pow]
    congr 1
    unfold EntropyTailQuantile.budgetScale
    rw [inv_pow, Real.sq_sqrt hB.le, div_eq_mul_inv, mul_comm]
  rw [hM]
  exact mean_square μ hfin ρ B hρ hρ4 hB

end ThresholdHC.FiniteGapCorollaries
