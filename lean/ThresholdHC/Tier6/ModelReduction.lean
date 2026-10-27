import ThresholdHC.Tier6.Specification

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

theorem populationRealization_of_process (hprocess : ProcessRealizationStatement) :
    PopulationRealizationStatement := by
  intro R _ μ _ A q
  constructor
  · unfold experimentLaw
    infer_instance
  · exact hprocess (PopulationSeed R) (populationSeedLaw μ A) (populationPolicy A)
      populationGap (populationPrior q) (measurable_populationPolicy A)
      measurable_populationGap (measurable_populationPrior q)
      populationGap_range (populationPrior_range q)

theorem minimaxLowerBound_of_algorithm (halgorithm : AlgorithmLowerBoundStatement) :
    MinimaxLowerBoundStatement := by
  intro μ _ B hB
  apply le_sInf
  intro r hr
  obtain ⟨R, mR, A, hbudget, rfl⟩ := hr
  exact halgorithm R μ A B hB hbudget

end ThresholdHC.Tier6
