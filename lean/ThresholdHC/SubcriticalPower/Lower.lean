import ThresholdHC.SubcriticalPower.Sublinear
import ThresholdHC.ConfidenceProgram.Lower
import ThresholdHC.EntropyTailSharp.TailRisk

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.SubcriticalPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open ThresholdHC.Genie ThresholdHC.Confidence ThresholdHC.ConfidenceProgram ThresholdHC.ConfidenceTransfer

/-- This lower bound holds for all exponents, including the saturated
budget range. It is sharp throughout the range below one. -/
theorem power_rms_lower (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B : ℝ}
    (hm : ExactPowerLaw μ α a) (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) :
    ENNReal.ofReal (min ρ ((EntropyTailQuantile.budgetScale B/a)^α)/32) ≤ rareMinimaxRisk μ ρ B := by
  have hh : 0 < EntropyTailQuantile.budgetScale B := inv_pos.mpr (Real.sqrt_pos.mpr hb)
  exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (power_tail_floor μ hm hr (by linarith) hh)
    (by norm_num : (0:ℝ) ≤ 32))).trans (ThresholdHC.EntropyTailSharp.quantile_tail_lower_general μ hr hu hb)

theorem power_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B δ : ℝ}
    (hm : ExactPowerLaw μ α a) (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B)
    (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ENNReal.ofReal (min ρ ((confidenceScale B δ/a)^α)/960) ≤ rareConfidenceRadius μ ρ B δ := by
  let β := B/Real.log (1/δ)
  have hl := confidence_log_pos hd hd'
  have hβ : 0 < β := div_pos hb hl
  have hscale : EntropyTailQuantile.budgetScale β = confidenceScale B δ := by
    simp only [EntropyTailQuantile.budgetScale,β,confidenceScale,Real.sqrt_div hb.le,Real.sqrt_div hl.le,inv_div]
  have h := (power_rms_lower μ hm hr hu hβ).trans (infinite_program_comparison μ ρ β hr (by linarith) hβ).1
  rw [hscale] at h
  have he := (ENNReal.div_le_div_right h 30).trans (stopping_confidence_lower μ hr (by linarith) hb hd hd')
  convert he using 1
  rw [← show ENNReal.ofReal (30:ℝ) = 30 from ENNReal.ofReal_ofNat 30,← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<30)]
  congr 1
  ring

end ThresholdHC.SubcriticalPower
