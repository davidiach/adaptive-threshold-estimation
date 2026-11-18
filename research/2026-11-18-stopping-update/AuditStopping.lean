import StoppingPopulation

open MeasureTheory PilotFeedback.Stopping
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (h : ∀ r, ∃ P : Plan, A.policy r = policy P) :
    ENNReal.ofReal (186844275/1000000000 : ℝ) ≤ maximalRMSRisk (Measure.dirac fifthGap) A :=
  rms_lower A h

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (h : ∀ r, ∃ P : Plan, A.policy r = policy P) :
    maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator <
      maximalRMSRisk (Measure.dirac fifthGap) A := rms_separation A h

#print axioms PilotFeedback.Stopping.certified
#print axioms PilotFeedback.Stopping.total
#print axioms PilotFeedback.Stopping.expect
#print axioms PilotFeedback.Stopping.four_lower
#print axioms PilotFeedback.Stopping.rms_lower
#print axioms PilotFeedback.Stopping.rms_separation
