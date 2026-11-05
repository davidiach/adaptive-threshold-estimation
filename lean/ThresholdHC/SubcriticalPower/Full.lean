import ThresholdHC.SubcriticalPower.Lower
import ThresholdHC.SubcriticalPower.Upper

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.SubcriticalPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open ThresholdHC.Confidence ThresholdHC.ConfidenceTransfer

/-- For 0 < α < 1 the exact minimax order is the smaller of the global
rarity and the αth power of the resolution divided by the margin scale.
The two upper estimators also work for every dominated CDF. -/
theorem sublinear_rates (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B δ : ℝ}
    (hα : 0 < α) (hu : α < 1) (ha : 0 < a) (hm : ExactPowerLaw μ α a)
    (hr : 0 < ρ) (hr' : ρ ≤ 1/4) (hb : 1 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let z := min ρ ((EntropyTailQuantile.budgetScale B/a)^α)
    let w := min ρ ((confidenceScale B δ/a)^α)
    (ENNReal.ofReal (z/32) ≤ rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal ((512/(1-α))*z)) ∧
    (ENNReal.ofReal (w/960) ≤ rareConfidenceRadius μ ρ B δ ∧
      rareConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal ((8192/(1-α))*w)) := by
  let z := min ρ ((EntropyTailQuantile.budgetScale B/a)^α)
  let w := min ρ ((confidenceScale B δ/a)^α)
  have hB : 0 < B := by linarith
  have hp := exactPower_margin μ α a hm
  refine ⟨⟨power_rms_lower μ hm hr hr' hB,?_⟩,⟨power_confidence_lower μ hm hr hr' hB hd hd',?_⟩⟩
  · obtain ⟨R,mR,A,hA⟩ := sublinear_rms_family hα hu ha hr.le hb
    obtain ⟨hw,hR⟩ := hA μ hp
    exact le_trans (sInf_le (show rareRisk μ A ρ ∈ _ from ⟨R,mR,A,hw,rfl⟩)) hR
  · obtain ⟨R,mR,A,hA⟩ := sublinear_confidence_family hα hu ha hr.le hb hd hd'
    obtain ⟨hw,hc⟩ := hA μ hp
    have hh : 0 < confidenceScale B δ := confidenceScale_pos hB hd hd'
    have hw' : 0 ≤ w := le_min hr.le (Real.rpow_nonneg (div_nonneg hh.le ha.le) _)
    exact sInf_le ⟨R,mR,A,_,mul_nonneg (div_nonneg (by norm_num) (by linarith)) hw',hw,hc,rfl⟩

end ThresholdHC.SubcriticalPower
