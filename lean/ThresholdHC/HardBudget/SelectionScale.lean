import ThresholdHC.HardBudget.BudgetScale
import ThresholdHC.EntropyTailSharp.Full
import ThresholdHC.QuantileSelection.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.EntropyTailQuantile

theorem selection_budget_scale (μ : Measure Gap) (ρ : ℝ) {b B : ℝ} (hb : 0 < b) (hB : b ≤ B) :
    selection μ ρ b ≤ ENNReal.ofReal (Real.sqrt (B/b))*selection μ ρ B := by
  obtain ⟨ha,he⟩ := budget_scale hb hB
  let a := Real.sqrt (B/b)
  have ha1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal a := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ha
  have hpos : ENNReal.ofReal a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
  have hobj (σ : Measure Gap) : selectionObjective μ ρ b σ ≤ ENNReal.ofReal a*selectionObjective μ ρ B σ := by
    unfold selectionObjective
    change 1/Real.sqrt b = a*(1/Real.sqrt B) at he
    rw [he,mul_add,ENNReal.ofReal_mul (zero_le_one.trans ha),mul_assoc]
    apply add_le_add le_rfl
    unfold tailCost
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro d
    change ENNReal.ofReal (min 1 (a*(1/Real.sqrt B)/(d:ℝ))) ≤ ENNReal.ofReal a * _
    rw [← ENNReal.ofReal_mul (zero_le_one.trans ha),mul_div_assoc]
    exact ENNReal.ofReal_le_ofReal (min_one_scaled _ _ ha)
  change selection μ ρ b ≤ ENNReal.ofReal a*selection μ ρ B
  unfold selection; rw [mul_min]
  apply le_min
  · exact (min_le_left _ _).trans (by simpa using mul_le_mul_left ha1 (ENNReal.ofReal ρ))
  · rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf; intro σ
    rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf; intro hs
    exact (min_le_right _ _).trans ((iInf_le_of_le σ (iInf_le _ hs)).trans (hobj σ))

theorem selection_saturates (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hb : 0 < B) (hu : B < 4) :
    selection μ ρ B = ENNReal.ofReal ρ := by
  rw [← quantile_selectionValue_eq]
  have hh : 1/2 ≤ EntropyTailQuantile.budgetScale B := by
    simpa only [EntropyTailQuantile.budgetScale,one_div] using half_le_inverse_sqrt hb hu
  exact (quantile_saturation (B := B) μ hr hr1 ((quantileThreshold_properties μ hr hr1).2.1.trans hh)).1

theorem finite_selection (μ : Measure Gap) (ρ B : ℝ) : selection μ ρ B ≠ ⊤ :=
  ((min_le_left _ _).trans_lt ENNReal.ofReal_lt_top).ne

end ThresholdHC.HardBudget
