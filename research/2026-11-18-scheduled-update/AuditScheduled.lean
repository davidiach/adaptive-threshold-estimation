import ScheduledPopulation

open MeasureTheory PilotFeedback.Scheduled
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (h : ∀ r, ∃ P : Plan, A.policy r = policy P) :
    ENNReal.ofReal (186960371/1000000000 : ℝ) ≤ maximalRMSRisk (Measure.dirac fifthGap) A :=
  rms_lower A h

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (h : ∀ r, ∃ P : Plan, A.policy r = policy P) :
    maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator <
      maximalRMSRisk (Measure.dirac fifthGap) A := rms_separation A h

#print axioms PilotFeedback.Scheduled.certified
#print axioms PilotFeedback.Scheduled.certificate_total
#print axioms PilotFeedback.Scheduled.expect
#print axioms PilotFeedback.Scheduled.four_lower
#print axioms PilotFeedback.Scheduled.rms_lower
#print axioms PilotFeedback.Scheduled.rms_separation
