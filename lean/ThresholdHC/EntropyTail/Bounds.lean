import ThresholdHC.EntropyTail.Objective
import ThresholdHC.EntropyTail.Specification

/-! The three elementary upper bounds for the selection functional and its value
for budgets of at most one flip. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

theorem selection_bounds : SelectionBoundsStatement := by
  intro ρ B _ _ _ μ _
  refine ⟨selection_le_rho μ ρ B, ?_, ?_⟩
  · have h := selection_le_objective (Measure.zero_le μ) ρ B
    rwa [selectionObjective_zero] at h
  · have h := selection_le_objective (le_refl μ) ρ B
    rwa [selectionObjective_self] at h

theorem small_budget : SmallBudgetStatement := by
  intro ρ B hρ hρ4 hB hB1 μ _
  unfold selection
  refine min_eq_left (le_trans (ENNReal.ofReal_le_ofReal ?_) (iInf_objective_lower μ hρ.le B))
  have hs0 : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hs1 : Real.sqrt B ≤ 1 := by
    have h := Real.sqrt_le_sqrt hB1
    rwa [Real.sqrt_one] at h
  have hh : 1 ≤ 1 / Real.sqrt B := by
    rw [le_div_iff₀ hs0]
    linarith
  have hr0 := Real.sqrt_nonneg ρ
  have hr1 : Real.sqrt ρ ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show ρ ≤ 1 by linarith)
    rwa [Real.sqrt_one] at h
  have hrr : ρ ≤ Real.sqrt ρ := by nlinarith [Real.mul_self_sqrt hρ.le]
  refine le_min ?_ (le_min (by linarith) (by linarith))
  nlinarith [mul_le_mul_of_nonneg_right hh hr0]

end ThresholdHC.EntropyTail
