import ThresholdHC.PilotFeedback.ScheduledPolicy
import ThresholdHC.LargeBudgetRMS.PilotWitness

/-! Target statements for the pilot-feedback separations at the gap `1/5` with
budget `25`, in the original population experiment.

The pilot flips 18 distinct coins once. At follow-up position `k = 1, …, 7` an
algorithm chooses a fresh coin, the `k`th pilot head or the `k`th pilot tail;
an unavailable revisit falls back to a fresh coin.
The adaptive witness `SharpRMS.Pilot.pilotEstimator` chooses each follow-up
after the previous answer; its worst RMS risk is below `0.186752`.

* A *precommitted* algorithm fixes all seven follow-up actions after the
  pilot, before any follow-up answer (`Ordered.policy`). The schedule may
  depend on the whole ordered pilot word.
* A *one-update* algorithm chooses after the pilot a split `m ∈ {0, …, 7}` and
  the first `m` actions, and the remaining `7 - m` actions after the first `m`
  answers (`Scheduled.policy`); either batch may be empty. The split and the
  first batch may depend on the ordered pilot word, the second batch on the
  ordered pilot and first-batch answers.

In both classes the seed may choose the plan, and the output may use the seed
and the whole tape. The component proofs in the other modules of this
directory are promoted unchanged from the research packages
`research/2026-11-18-pilot-feedback` and `research/2026-11-18-scheduled-update`;
`Full.lean` adds the RMS form of the precommitted results, and the one-update
targets are that package's `rms_lower` and `rms_separation`. -/
noncomputable section
namespace ThresholdHC.PilotFeedback
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

/-- Every precommitted algorithm has worst RMS risk at least `0.18735887`. -/
def PrecommittedLowerStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ s : Ordered.Schedule, A.policy r = Ordered.policy s) →
    ENNReal.ofReal (18735887/100000000 : ℝ) ≤
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A

/-- The adaptive witness has strictly smaller worst RMS risk than every
precommitted algorithm. -/
def PrecommittedSeparationStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ s : Ordered.Schedule, A.policy r = Ordered.policy s) →
    maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap)
        ThresholdHC.SharpRMS.Pilot.pilotEstimator <
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A

/-- Every one-update algorithm has worst RMS risk at least `0.186960371`. -/
def OneUpdateLowerStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : Scheduled.Plan, A.policy r = Scheduled.policy P) →
    ENNReal.ofReal (186960371/1000000000 : ℝ) ≤
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A

/-- The adaptive witness has strictly smaller worst RMS risk than every
one-update algorithm. -/
def OneUpdateSeparationStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : Scheduled.Plan, A.policy r = Scheduled.policy P) →
    maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap)
        ThresholdHC.SharpRMS.Pilot.pilotEstimator <
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A

end ThresholdHC.PilotFeedback
