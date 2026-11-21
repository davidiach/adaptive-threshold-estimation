import ThresholdHC.OracleSharpness.Sharpness

/-! Sharpness of the oracle upper coefficient one half for both magnitude
oracles, and the auxiliary ordinary-model bound behind it, stated against the
specification. -/
noncomputable section
namespace ThresholdHC.OracleSharpness
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

theorem oracle_upper_sharpness : OracleUpperSharpnessStatement := oracle_small_gap_sharp

theorem small_gap_sign_lower : SmallGapSignLowerStatement := small_gap_minimax_lower

end ThresholdHC.OracleSharpness
