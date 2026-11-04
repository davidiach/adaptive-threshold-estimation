import ThresholdHC.SelectionStability.Variation
import ThresholdHC.SelectionStability.Rounding
import ThresholdHC.QuantileSelection.Full

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.SelectionStability
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Corollary 9. Transport an enclosure of the rounded selection value back to the original law. -/
theorem transfer_enclosure (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap) (hm : Measurable T) {r η ρ B L U : ℝ} (hr : 1 ≤ r)
    (hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hB : 0 < B) (hη : tvDist μ μ₀ / 2 ≤ η)
    (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ))
    (hb : ∀ j, T ⁻¹' band j = band j)
    (hl : L ≤ (selection (μ₀.map T) ρ B).toReal) (hu : (selection (μ₀.map T) ρ B).toReal ≤ U) :
    max 0 (L-η) ≤ (selection μ ρ B).toReal ∧ (selection μ ρ B).toReal ≤ min ρ (r*U+η) := by
  have hf (ξ : Measure Gap) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (selection_le_rho ξ ρ B)
  obtain ⟨hdown,hup⟩ := band_preserving_rounding μ₀ T hm hr hρ hrho hB hd hb
  have h₁ := ENNReal.toReal_mono (hf μ₀) hdown
  have h₂ := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf _)) hup
  have hr₀ := zero_le_one.trans hr
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr₀] at h₂
  have hv := abs_le.mp ((total_variation_stability μ μ₀ hρ hrho hB).trans hη)
  have hcap := ENNReal.toReal_mono ENNReal.ofReal_ne_top (selection_le_rho μ ρ B)
  rw [ENNReal.toReal_ofReal hρ.le] at hcap
  exact ⟨max_le ENNReal.toReal_nonneg (by linarith only [hl,h₁,hv.1]),
    le_min hcap (by linarith only [hv.2,h₂,mul_le_mul_of_nonneg_left hu hr₀])⟩

/-- The computable quantile choice gives the lower endpoint (5/8)Q minus the discarded mass. -/
theorem quantile_enclosure (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap) (hm : Measurable T) {r η ρ B : ℝ} (hr : 1 ≤ r)
    (hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hB : 0 < B) (hη : tvDist μ μ₀ / 2 ≤ η)
    (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ))
    (hb : ∀ j, T ⁻¹' band j = band j) :
    let Q := (EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal
    max 0 (5/8*Q-η) ≤ (selection μ ρ B).toReal ∧ (selection μ ρ B).toReal ≤ min ρ (r*Q+η) := by
  let ν := μ₀.map T
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  obtain ⟨hl,hu⟩ := QuantileSelection.locked_selection_comparison ν hρ hrho hB
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (selection_le_rho ν ρ B)
  have hupper := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf) hu
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (8/5:ℝ))] at hupper
  apply transfer_enclosure μ μ₀ T hm hr hρ hrho hB hη hd hb
  · dsimp only [ν] at hupper
    linarith only [hupper]
  · exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)) hl

end ThresholdHC.SelectionStability
