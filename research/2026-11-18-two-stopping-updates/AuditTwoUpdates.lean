import TwoUpdatePopulation

open MeasureTheory PilotFeedback.TwoUpdates
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (h : ∀ r, ∃ P : Plan, A.policy r = policy P) :
    ENNReal.ofReal (186764460/1000000000 : ℝ) ≤ maximalRMSRisk (Measure.dirac fifthGap) A :=
  rms_lower A h

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (h : ∀ r, ∃ P : Plan, A.policy r = policy P) :
    maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator <
      maximalRMSRisk (Measure.dirac fifthGap) A := rms_separation A h

#print axioms PilotFeedback.TwoUpdates.certified
#print axioms PilotFeedback.TwoUpdates.total
#print axioms PilotFeedback.TwoUpdates.expect
#print axioms PilotFeedback.TwoUpdates.four_lower
#print axioms PilotFeedback.TwoUpdates.rms_lower
#print axioms PilotFeedback.TwoUpdates.rms_separation
