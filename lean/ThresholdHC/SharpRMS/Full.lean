import ThresholdHC.SharpRMS.Specification
import ThresholdHC.SharpRMS.Unrestricted
import ThresholdHC.SharpRMS.OracleAttainment

/-! The sharp universal RMS lower coefficient in the ordinary experiment and
under both magnitude oracles, stated against the specification. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

theorem sharp_lower : SharpLowerStatement := @unrestricted_minimax_lower

theorem sharp_coefficient : SharpCoefficientStatement := universal_coefficient_iff

theorem sharp_endpoint : SharpEndpointStatement := endpoint_minimax_eq

theorem large_budget_lower : LargeBudgetLowerStatement := @large_budget_minimax_lower

theorem gap_reduction : GapReductionStatement := @critical_gap_reduction

theorem oracle_sharp_lower : OracleSharpLowerStatement := @oracle_minimax_lower

theorem oracle_large_budget_lower_bound : OracleLargeBudgetLowerStatement := @oracle_large_budget_lower

theorem oracle_endpoint : OracleEndpointStatement := oracle_endpoint_eq

end ThresholdHC.SharpRMS
