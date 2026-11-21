import ThresholdHC.StoppingUpdate.Specification
import ThresholdHC.StoppingUpdate.StoppingPopulation
import ThresholdHC.StoppingUpdate.StoppingEmbedding

/-! One schedule replacement at a stopping time, at the gap `1/5` with budget
`25`: every such algorithm has worst RMS risk at least `0.186844275`, and the
adaptive witness, whose worst RMS risk is at most `0.186752`, is strictly
better. The targets are the research package's `rms_lower` and
`rms_separation` (`research/2026-11-18-stopping-update`). The component
`scheduled_embeds` shows that this class contains the one-update class of
`PilotFeedback.OneUpdateLowerStatement`, whose split is fixed after the pilot. -/
namespace ThresholdHC.StoppingUpdate

theorem one_stopping_update_rms_lower : OneStoppingUpdateLowerStatement := by
  intro R _ A hc
  exact rms_lower A hc

theorem one_stopping_update_rms_separation : OneStoppingUpdateSeparationStatement := by
  intro R _ A hc
  exact rms_separation A hc

/-- A scheduled one-update plan is a one-stopping-update plan whose trigger
fires at the prefix of length `18 + split`. -/
theorem scheduled_embeds (P : ThresholdHC.PilotFeedback.Scheduled.Plan) :
    ∃ Q : Plan, policy Q = ThresholdHC.PilotFeedback.Scheduled.policy P :=
  ⟨_, policy_of_scheduled P⟩

end ThresholdHC.StoppingUpdate
