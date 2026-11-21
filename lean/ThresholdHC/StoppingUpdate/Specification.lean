import ThresholdHC.PilotFeedback.OrderedPolicy
import ThresholdHC.LargeBudgetRMS.PilotWitness

/-! Target statements for one schedule replacement at a stopping time, at the
gap `1/5` with budget `25`, in the original population experiment.

Source: `research/2026-11-18-stopping-update/README.md` (section *One update at
a stopping time*) and its public statements in
`research/2026-11-18-stopping-update/AuditStopping.lean`; the claim is
summarized in `docs/RESULTS.md`, section *Minimax law and unbiasedness*
(the paragraph on letting the update time depend on the follow-up answers).
It is not in the paper.

The pilot flips 18 distinct coins once. At follow-up position `k = 1, …, 7`
an algorithm chooses a fresh coin, the `k`th pilot head or the `k`th pilot
tail; an unavailable revisit falls back to a fresh coin. A
*one-stopping-update* algorithm (`Plan`, `policy`) follows an initial
seven-action schedule chosen from the ordered pilot word. Before each
follow-up action it may use every answer so far to decide whether to trigger
(`Plan.trigger`, read on prefixes of length at least 18). At the first
triggering prefix `z` the remaining actions are replaced by the schedule
`Plan.second z`, which then stays fixed on every extension of `z`. Triggering
immediately after the pilot, before the final action, or never are all
allowed. The seed may choose the plan, and the output may use the seed and
the whole tape.

The adaptive witness `SharpRMS.Pilot.pilotEstimator` has worst RMS risk at most
`0.186752` (Lean-checked). The definitions below are those of the research module
`StoppingPolicy.lean`, with the namespace `PilotFeedback.Stopping` renamed to
`ThresholdHC.StoppingUpdate`. -/
noncomputable section
namespace ThresholdHC.StoppingUpdate
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

/-- The initial schedule reads the pilot. The first trigger on an observed
prefix locks in the replacement schedule for the rest of the experiment. -/
structure Plan where
  first : PilotFeedback.Ordered.Schedule
  trigger : List Bool → Bool
  second : PilotFeedback.Ordered.Schedule

/-- First triggering prefix of length between 18 and n, inclusive. -/
def boundary (P : Plan) (word : List Bool) : ℕ → Option (List Bool)
  | 0 => none
  | n+1 => (boundary P word n).orElse fun _ =>
      if 18 ≤ n+1 ∧ P.trigger (word.take (n+1)) then some (word.take (n+1)) else none

/-- The schedule in force at follow-up position `k`: the initial one until a
prefix of length at most `18 + k` triggers, then the replacement chosen there. -/
def frozen (P : Plan) (word : List Bool) : PilotFeedback.Ordered.Schedule := fun v k =>
  match boundary P word (18+k) with
  | none => P.first v k
  | some z => P.second z k

/-- The coin label requested after the ordered answer word `xs`. -/
def label (P : Plan) (xs : List Bool) := PilotFeedback.Ordered.label (frozen P xs) xs

/-- The policy of a one-stopping-update plan, stopped after 25 flips. -/
def policy (P : Plan) := HardBudget.stopAt 25 (label P)

/-- Every algorithm whose seed selects a one-stopping-update plan has worst RMS
risk at least `0.186844275`. -/
def OneStoppingUpdateLowerStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : Plan, A.policy r = policy P) →
    ENNReal.ofReal (186844275/1000000000 : ℝ) ≤
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A

/-- The adaptive witness has strictly smaller worst RMS risk than every
algorithm whose seed selects a one-stopping-update plan. -/
def OneStoppingUpdateSeparationStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : Plan, A.policy r = policy P) →
    maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap)
        ThresholdHC.SharpRMS.Pilot.pilotEstimator <
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A

end ThresholdHC.StoppingUpdate
