import ThresholdHC.Tier3.RandomizedModel
import ThresholdHC.Tier3.StoppingModel
import ThresholdHC.Tier3.OptimizerModel
import ThresholdHC.Tier3.ExamplesModel

/-! The Tier 3 landmark, fixed before any proof checkpoint is accepted. -/
namespace ThresholdHC.Tier3

def Tier3LandmarkStatement : Prop :=
  RandomizedTotalStatement ∧ RandomizedInformationStatement ∧
  RandomizedMarginalKLStatement ∧ RandomizedTestingStatement ∧
  FiniteWorkStopsStatement ∧ UnboundedStoppingStatement ∧ UnboundedTestingStatement ∧
  ArbitraryLawCutoffStatement ∧ ArbitraryLawOptimizerStatement ∧ UnboundedExampleStatement

end ThresholdHC.Tier3
