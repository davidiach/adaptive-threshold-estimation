import ThresholdHC.RevisitUpper.Specification
import ThresholdHC.RevisitUpper.LabelRule
import ThresholdHC.RevisitUpper.RevisitWitness

/-! The 20+5 revisit witness, stated against the specification. The witness is
`revisitEstimator` with the library reader `SharpRMS.Revisit.label` and the
rational table `estimate`. -/
noncomputable section
namespace ThresholdHC.RevisitUpper
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6

theorem revisit_witness : RevisitWitnessStatement :=
  ⟨SharpRMS.Revisit.label, revisitEstimator, estimate, label_rule, fun _ => rfl, fun _ => rfl,
    revisit_cap, @revisit_budget,
    iSup_le fun q => HardBudget.rms_from_square _ _ _ _ (by norm_num) (revisit_squared_risk q)⟩

end ThresholdHC.RevisitUpper
