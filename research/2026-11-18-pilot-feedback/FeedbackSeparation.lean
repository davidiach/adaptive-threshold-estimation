import FeedbackComparison
import PilotWitness

open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

namespace PilotFeedback

/-- The full worst-case MSE of the adaptive witness is strictly below the
four-point worst MSE of any randomized precommitted grouped rule. -/
theorem strict_separation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → Rule)
    (hm : ∀ i, Measurable fun z => ENNReal.ofReal (pointMSE (r z) i)) :
    (⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) <
      worstFour μ r := by
  rw [pilot_worst_squared]
  apply lt_of_lt_of_le _ (worstFour_lower μ r hm)
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2
  norm_num [endpoint]

end PilotFeedback
