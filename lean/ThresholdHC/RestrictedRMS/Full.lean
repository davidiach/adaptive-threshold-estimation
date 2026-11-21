import ThresholdHC.RestrictedRMS.Restricted

/-! The restricted-setting RMS coefficients of rms-gap.tex, stated against the
specification. -/
noncomputable section
namespace ThresholdHC.RestrictedRMS

theorem small_budget_coefficient : SmallBudgetCoefficientStatement :=
  small_budget_coefficient_iff

theorem oracle_small_budget_coefficient : OracleSmallBudgetCoefficientStatement :=
  oracle_small_budget_coefficient_iff

theorem restricted_coefficient : RestrictedCoefficientStatement :=
  restricted_coefficient_iff

theorem three_flip_coefficient : ThreeFlipCoefficientStatement :=
  three_flip_coefficient_iff

end ThresholdHC.RestrictedRMS
