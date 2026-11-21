import ThresholdHC.FiniteGapCorollaries.Corollaries

/-! Corollary `cor:one-gap` and both displays of Corollary `cor:mse` of the
finite-gap manuscript. -/
noncomputable section
namespace ThresholdHC.FiniteGapCorollaries

theorem one_gap_rate : OneGapStatement := by
  intro d ρ B hρ hρ4 hB
  exact one_gap d ρ B hρ hρ4 hB

theorem mean_square_form : MeanSquareStatement := by
  intro μ _ hfin ρ B hρ hρ4 hB
  exact mean_square μ hfin ρ B hρ hρ4 hB

theorem large_budget_mean_square_form : LargeBudgetMeanSquareStatement := by
  intro μ _ hfin ρ B hρ hρ4 hB hlarge
  exact large_budget_mean_square μ hfin ρ B hρ hρ4 hB hlarge

end ThresholdHC.FiniteGapCorollaries
