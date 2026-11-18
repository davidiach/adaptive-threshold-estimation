import ThresholdHC.LargeBudgetRMS.Specification
import ThresholdHC.LargeBudgetRMS.MultiBiasBounds
import ThresholdHC.LargeBudgetRMS.PilotWitness

/-! The coefficient of the RMS lower bound at budgets of at least 25 lies in
[0.175198, 0.186752], stated against the specification. -/
noncomputable section
namespace ThresholdHC.LargeBudgetRMS
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

theorem bracket_lower : BracketLowerStatement := @SharpRMS.MultiBias.lower_25

theorem hundred_lower : HundredLowerStatement := @SharpRMS.MultiBias.lower_100

theorem fifth_gap_upper : FifthGapUpperStatement := SharpRMS.Pilot.pilot_upper_25

theorem bracket_upper : BracketUpperStatement := SharpRMS.Pilot.pilot_coefficient_upper

end ThresholdHC.LargeBudgetRMS
