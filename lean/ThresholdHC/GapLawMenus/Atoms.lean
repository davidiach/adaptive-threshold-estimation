import ThresholdHC.GapLawMenus.Full

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.GapLawMenus
open ThresholdHC.Tier6 ThresholdHC.EntropyTail

/-- Concrete inverse-square menu costs are finite sums of atom weights. -/
theorem cost_atomic (μ : Measure Gap) [IsFiniteMeasure μ] (S : Finset Gap) :
    cost μ S = ∑ d ∈ S, (μ {d}).toReal * ((d:ℝ)⁻¹)^2 := by
  rw [cost,costMass,lintegral_finset,ENNReal.toReal_sum
    (fun d _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ {d}))]
  apply Finset.sum_congr rfl
  intro d _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)]
  ring

/-- Concrete saved ordinary cost is the exact finite weighted tail sum. -/
theorem saving_atomic (μ : Measure Gap) [IsFiniteMeasure μ] (S : Finset Gap)
    {h : ℝ} (hh : 0 ≤ h) :
    saving μ h S = ∑ d ∈ S, (μ {d}).toReal * min 1 (h/(d:ℝ)) := by
  rw [saving,tailCost,lintegral_finset,ENNReal.toReal_sum
    (fun d _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ {d}))]
  apply Finset.sum_congr rfl
  intro d _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal
    (le_min zero_le_one (div_nonneg hh d.property.1.le))]
  ring

end ThresholdHC.GapLawMenus

