import ThresholdHC.SharpStrict.Strict

/-! Strictness of the sharp universal RMS lower bound away from the budget
four, in the ordinary experiment and under both magnitude oracles, stated
against the specification. -/
noncomputable section
namespace ThresholdHC.SharpStrict
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

theorem strict_sharp_lower : StrictSharpLowerStatement := @minimax_strict_lower

theorem strict_coefficient : StrictCoefficientStatement := uniform_strict_coefficient

theorem sharp_equality_case : SharpEqualityCaseStatement := @equality_forces_four

theorem small_budget_lower : SmallBudgetLowerStatement := @small_budget_minimax_lower_four

theorem critical_strict : CriticalStrictStatement := critical_point_strict

theorem oracle_strict_sharp_lower : OracleStrictSharpLowerStatement := @oracle_minimax_strict

end ThresholdHC.SharpStrict
