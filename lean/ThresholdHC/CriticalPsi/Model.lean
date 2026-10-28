import ThresholdHC.Tier3.OptimizerModel
import ThresholdHC.CriticalEntropy.CriticalLaw

noncomputable section
namespace ThresholdHC.CriticalPsi
open MeasureTheory Set ThresholdHC.Tier3 ThresholdHC.CriticalEntropy

/-- The actual variational supremum over all measurable feasible allocations.
The objective and global mass constraint are the existing arbitrary-law ones. -/
def criticalPsi (ρ h : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ v : ℝ → ℝ, FeasibleAllocation criticalGapLaw ρ v ∧
    y = rareObjective criticalGapLaw id h v}

end ThresholdHC.CriticalPsi
