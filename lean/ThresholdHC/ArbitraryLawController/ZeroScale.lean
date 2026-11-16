import ThresholdHC.ArbitraryLawAdaptation.ZeroModel
import ThresholdHC.HardBudget.SelectionScale

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.HardBudget

theorem finite_zeroSelection (α : Measure ℝ) (ρ B : ℝ) : zeroSelection α ρ B ≠ ⊤ :=
  ((min_le_left _ _).trans_lt ENNReal.ofReal_lt_top).ne

theorem zeroSelection_antitone (α : Measure ℝ) (ρ : ℝ) {b B : ℝ}
    (hb : 0 < b) (hB : b ≤ B) : zeroSelection α ρ B ≤ zeroSelection α ρ b := by
  have hs : 1 / Real.sqrt B ≤ 1 / Real.sqrt b :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hb) (Real.sqrt_le_sqrt hB)
  unfold zeroSelection
  apply min_le_min le_rfl
  apply iInf_mono; intro σ
  apply iInf_mono; intro _
  unfold zeroObjective
  apply add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hs) le_rfl)
  apply lintegral_mono
  intro d
  by_cases hd : d ≤ 0
  · simp [zeroTailWeight, hd]
  · simp only [zeroTailWeight, hd, ite_false]
    exact ENNReal.ofReal_le_ofReal
      (min_le_min_left _ (div_le_div_of_nonneg_right hs (not_le.mp hd).le))

theorem zeroSelection_budget_scale (α : Measure ℝ) (ρ : ℝ) {b B : ℝ}
    (hb : 0 < b) (hB : b ≤ B) :
    zeroSelection α ρ b ≤ ENNReal.ofReal (Real.sqrt (B/b)) * zeroSelection α ρ B := by
  obtain ⟨ha, he⟩ := budget_scale hb hB
  let a := Real.sqrt (B/b)
  have ha1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ha
  have hpos : ENNReal.ofReal a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
  have hobj (σ : Measure ℝ) : zeroObjective α ρ b σ ≤ ENNReal.ofReal a * zeroObjective α ρ B σ := by
    unfold zeroObjective
    change 1 / Real.sqrt b = a * (1 / Real.sqrt B) at he
    rw [he, mul_add, ENNReal.ofReal_mul (zero_le_one.trans ha), mul_assoc]
    apply add_le_add le_rfl
    unfold zeroTailCost
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro d
    by_cases hd : d ≤ 0
    · simpa only [zeroTailWeight, hd, ite_true, mul_one] using ha1
    · simp only [zeroTailWeight, hd, ite_false]
      rw [← ENNReal.ofReal_mul (zero_le_one.trans ha), mul_div_assoc]
      exact ENNReal.ofReal_le_ofReal (min_one_scaled _ _ ha)
  change zeroSelection α ρ b ≤ ENNReal.ofReal a * zeroSelection α ρ B
  unfold zeroSelection
  rw [mul_min]
  apply le_min
  · exact (min_le_left _ _).trans (by simpa using mul_le_mul_left ha1 (ENNReal.ofReal ρ))
  · rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf; intro σ
    rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf; intro hs
    exact (min_le_right _ _).trans ((iInf_le_of_le σ (iInf_le _ hs)).trans (hobj σ))

end ThresholdHC.ArbitraryLawController
