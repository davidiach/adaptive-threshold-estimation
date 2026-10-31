import ThresholdHC.EntropyTailQuantile.QuantileSplitFull
import ThresholdHC.EntropyTailQuantile.QuantileTailBound
import ThresholdHC.EntropyTailQuantile.QuantileCoreBound
import ThresholdHC.EntropyTailQuantile.QuantileRootBound

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

theorem entropy_root_eq_ofReal {G : ℝ≥0∞} (hG : G ≠ ⊤) {ρ h : ℝ}
    (hρ : 0 ≤ ρ) (hh : 0 ≤ h) :
    ENNReal.ofReal h * (ENNReal.ofReal ρ * G)^(1/(2:ℝ)) =
      ENNReal.ofReal (h * sqrt (ρ * G.toReal)) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hG]
  rw [← ENNReal.ofReal_mul hρ, ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg hρ ENNReal.toReal_nonneg) (by norm_num), ← sqrt_eq_rpow,
    ← ENNReal.ofReal_mul hh]

theorem quantile_comparison_pointwise (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hht : budgetScale B < quantileThreshold μ ρ) (σ : Measure Gap) (hσ : σ ≤ μ) :
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (1+2*sqrt 2) *
      selectionCost μ σ ρ (budgetScale B) := by
  have hh := budgetScale_pos hB
  have ht := (quantileThreshold_properties μ hρ hρ1).1
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have hfactor : (0:ℝ) < 1+2*sqrt 2 := by positivity
  by_cases hG : measureCostEntropy σ = ⊤
  · have he : selectionCost μ σ ρ (budgetScale B) = ⊤ := by
      simp [selectionCost, hG, ENNReal.mul_top, ENNReal.ofReal_eq_zero,
        not_le.mpr hρ, not_le.mpr hh]
    rw [he]
    simp [ENNReal.mul_top, ENNReal.ofReal_eq_zero, not_le.mpr hfactor]
  let h := budgetScale B
  let t := quantileThreshold μ ρ
  let T := tailModulus (quantileTail μ ρ) h
  let A := (measureCostEntropy σ).toReal
  let C := (measureCostEntropy (quantileCore μ ρ)).toReal
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂upperCut t (quantileBoundaryFraction μ ρ) (μ-σ)
  let x := h * sqrt (ρ*A)
  let y := tailModulus (μ-σ) h
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hH : 0 ≤ H := integral_nonneg (fun d : Gap => inv_nonneg.mpr d.property.1.le)
  have hT : 0 ≤ T := tailModulus_nonneg _ hh.le
  have hx : 0 ≤ x := mul_nonneg hh.le (sqrt_nonneg _)
  have hy : 0 ≤ y := tailModulus_nonneg _ hh.le
  have hcore : measureCostEntropy (quantileCore μ ρ) ≠ ⊤ :=
    (measureCostEntropy_lt_top_of_support _ ht (quantileCore_support μ ρ)).ne
  have hcost : C ≤ 2*A+(8/t)*H := by
    have hb := quantileCore_entropy_bound μ hρ hρ1 σ hσ
    have hn : 0 ≤ (8/t)*H := mul_nonneg (div_nonneg (by norm_num) ht.le) hH
    have he : 2 * measureCostEntropy σ + ENNReal.ofReal ((8/t)*H) =
        ENNReal.ofReal (2*A+(8/t)*H) := by
      rw [ENNReal.ofReal_add (by positivity) hn, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp only [A, ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hG]
    rw [he] at hb
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hobj : selectionCost μ σ ρ h = ENNReal.ofReal (x+y) := by
    rw [selectionCost, entropy_root_eq_ofReal hG hρ.le hh.le,
      ← ENNReal.ofReal_add hx hy]
  have hTS : T ≤ x+y := by
    apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg hx hy)).mp
    rw [← hobj]
    exact quantileTail_le_selectionCost μ hρ hρ1 hh.le σ hσ
  have hroot : h * sqrt (ρ*C) ≤ sqrt 2*x + sqrt (8*T*y) :=
    quantile_root_bound hh.le hρ.le hA hC hH hT hcost
      (quantileTail_threshold_lower μ hρ hρ1 hh.le hht)
      (quantileCore_residual_work μ hρ hρ1 hh.le hht σ)
  have hfinal : T+h*sqrt (ρ*C) ≤ (1+2*sqrt 2)*(x+y) :=
    quantile_comparison_algebra hx hy hTS (by linarith only [hroot])
  calc
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal T +
        ENNReal.ofReal h * (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ))^(1/(2:ℝ)) :=
      min_le_right _ _
    _ = ENNReal.ofReal (T+h*sqrt (ρ*C)) := by
      rw [entropy_root_eq_ofReal hcore hρ.le hh.le, ← ENNReal.ofReal_add hT (by positivity)]
    _ ≤ ENNReal.ofReal ((1+2*sqrt 2)*(x+y)) := ENNReal.ofReal_le_ofReal hfinal
    _ = _ := by rw [ENNReal.ofReal_mul hfactor.le, ← hobj]

/-- The paper's full arbitrary-law comparison, including atomic gap laws. -/
theorem quantile_comparison : QuantileComparisonStatement := by
  intro μ _ ρ B hρ hρ4 hB
  have hρ1 : ρ ≤ 1 := by linarith
  refine ⟨selectionValue_le_closedQuantileValue μ hρ hρ1 B, ?_⟩
  have hf : (1:ℝ) ≤ 1+2*sqrt 2 := le_add_of_nonneg_right (by positivity)
  have hfE : (1:ℝ≥0∞) ≤ ENNReal.ofReal (1+2*sqrt 2) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hf
  have hf0 : ENNReal.ofReal (1+2*sqrt 2) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hfE)
  by_cases ht : quantileThreshold μ ρ ≤ budgetScale B
  · obtain ⟨hK, hQ⟩ := quantile_saturation μ hρ hρ1 ht
    rw [hK, hQ]
    simpa only [one_mul] using mul_le_mul_left hfE (ENNReal.ofReal ρ)
  · have hht := lt_of_not_ge ht
    unfold selectionValue
    rw [mul_min]
    apply le_min
    · exact (min_le_left _ _).trans (by
        simpa only [one_mul] using mul_le_mul_left hfE (ENNReal.ofReal ρ))
    · rw [ENNReal.mul_iInf_of_ne hf0 ENNReal.ofReal_ne_top]
      apply le_iInf
      intro σ
      rw [ENNReal.mul_iInf_of_ne hf0 ENNReal.ofReal_ne_top]
      apply le_iInf
      exact quantile_comparison_pointwise μ hρ hρ1 hB hht σ

end ThresholdHC.EntropyTailQuantile
