import ThresholdHC.Tier6.AlgorithmModel

noncomputable section
open MeasureTheory
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

/-- Every admissible policy has the explicitly constructed infinite experiment.
The finite-cylinder identity is a conclusion, not an assumed model field. -/
def ProcessRealizationStatement : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ)
    (hp : MeasurableCreationPolicy pol) (hdm : MeasurableEnvironment d)
    (hqm : MeasurableEnvironment q)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (hq : ∀ u i, 0 ≤ q u i ∧ q u i ≤ 1),
    RealizesCreationPrefixes μ (creationProcessLaw μ pol d q hp hdm hqm hd hq)
      Prod.fst Prod.snd pol d q

def Tier6LandmarkStatement : Prop :=
  ProcessRealizationStatement ∧ PopulationRealizationStatement ∧
  HardPairValidityStatement ∧ HardPairSeparationStatement ∧ ModulusScalingStatement ∧
  BudgetHardPairStatement ∧ TwoPointRiskStatement ∧ BudgetClassNonemptyStatement ∧
  AlgorithmLowerBoundStatement ∧ MinimaxLowerBoundStatement

end ThresholdHC.Tier6
